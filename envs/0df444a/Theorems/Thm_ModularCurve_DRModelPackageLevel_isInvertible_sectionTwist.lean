-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_isInvertible_sectionTwist
-- name    : ModularCurve.DRModelPackageLevel.isInvertible_sectionTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/6059af29-37f7-587d-928a-a29875f6c5d9
-- title:
--   Invertibility of section twists at smooth A-points
-- statement:
--   Fix $N_0$ nonzero and a prime $p$ with $p \nmid N_0$, and let $\mathfrak{P}$ be a `DRModelPackageLevel N₀ p hpN₀`, i.e. a bundle of data and properties for the structure morphism `toBase N₀ p` from `X N₀ p` to $\operatorname{Spec}(R\,p)$ (properness, flatness, integrality, normality, a generic fibre identification with a curve model of the modular function field, distinguished sections, and an open part named `smoothLocus`). Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, and let $\rho : R\,p \to A$ be a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map $R\,p \to \overline{\mathbb{Q}}$. Let $n$ be a natural number and $s : \mathrm{Fin}\,n \to$ (morphisms $\operatorname{Spec} A \to X\,N_0\,p$ whose composite with `toBase N₀ p` is $\operatorname{Spec}(\rho)$), and assume the topological image of each $s_i$ lies in `𝔓.smoothLocus`. For each $i$, `RelEffCartierDiv.ofPoint` gives the relative effective Cartier divisor of degree one on the pullback $X\,N_0\,p \times_{\operatorname{Spec}(R\,p)} \operatorname{Spec} A$ cut out by the graph ideal sheaf $I_i$ of $s_i$. The conclusion is that for all exponent functions $\mathrm{pos}, \mathrm{neg} : \mathrm{Fin}\,n \to \mathbb{N}$ the module obtained by right-folding $M \mapsto (I_i^{\mathrm{pos}\,i})^{\vee} \otimes (I_i^{\mathrm{neg}\,i}) \otimes M$ over `List.finRange n`, starting from the unit module, is invertible: every point of the pullback has an open neighbourhood over which the restriction of this module is isomorphic to the unit sheaf of modules.
--
--   This is the statement that a twist $\bigotimes_i \mathcal{O}(s_i)^{\mathrm{pos}\,i} \otimes \mathcal{O}(-s_i)^{\mathrm{neg}\,i}$ by $A$-valued sections landing in the smooth locus of the Deligne–Rapoport model is a line bundle on the base change of the model to $A$. It is used when such a twist of total degree zero is fed to the relative Picard functor, and is cited in the construction of the $A$-point of $\operatorname{Pic}^0$ attached to a section twist and in the computations of its fibres and residue-field specialisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_isInvertible_sectionTwist.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard IsLocalRing ModularCurve ModularCurve.DRLevel

theorem ModularCurve.DRModelPackageLevel.isInvertible_sectionTwist
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    {n : ℕ} (s : Fin n → SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
    (hsm : ∀ i, Set.range (s i).1.base ⊆ (𝔓.smoothLocus : Set (X N₀ p))) :
    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := instDecidableEqResidueFieldSemistable A
    haveI : IsProper (toBase N₀ p) := 𝔓.isProper
    ∀ (pos neg : Fin n → ℕ),
      Scheme.Modules.IsInvertible
        ((List.finRange n).foldr
            (fun i M => ((RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I ^ (pos i)).invModule ⊗
              ((RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I ^ (neg i)).module ⊗ M)
            (𝟙_ (pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))).Modules)) := by sorry
