-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_nonempty_rigidify_pullbackCurve_comp1_sectionTwist_iso
-- name    : ModularCurve.DRModelPackageLevel.nonempty_rigidify_pullbackCurve_comp1_sectionTwist_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/65194035-8c38-5007-a671-c1794954002b
-- title:
--   Restriction of the rigidified section twist to the second component
-- statement:
--   Fix $N_0 \neq 0$ and a prime $p$ with $p \nmid N_0$, a Deligne–Rapoport model package $\mathfrak{P} :$ `DRModelPackageLevel N₀ p hpN₀`, a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p \in A.\mathrm{nonunits}$, and a ring map $\rho : R_p \to A$ whose composite with $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map; the residue field $\kappa =$ `ResidueField ↥A` then has characteristic $p$ and is an $R_p$-algebra via `residue ↥A` composed with $\rho$. Assume the base change of `toBase0 N₀ p` to $\kappa$ is proper, and let: $\varepsilon_0$ be a section of `toBase0 N₀ p` over $\mathrm{Spec}\,R_p$; $s : \mathrm{Fin}\,n \to$ morphisms $\mathrm{Spec}\,A \to X(N_0,p)$ lying over `Spec.map ρ`, each with image contained in the open set $\mathfrak{P}.\mathrm{smoothLocus}$; $c : \mathrm{Fin}\,n \to \mathrm{Fin}\,2$; $y_i$ $\kappa$-points of `fibre` whose first projection is $s_i$ composed with `Spec.map (residue ↥A)` and whose second projection is the identity; $z_i$ sections of the base change of `toBase0 N₀ p` to $\kappa$ with $z_i$ followed by the component morphism $\mathfrak{P}.\mathrm{comp}$ of index $c_i$ equal to $y_i$, and with the image of the closed point under $y_i$ outside the range of the component morphism of index $1 - c_i$; $\psi_{\mathrm{red}}$ the morphism `Spec.map (residue ↥A)` viewed over the base; and $\mathrm{pos}, \mathrm{neg} : \mathrm{Fin}\,n \to \mathbb{N}$. Then the following two modules on the pullback of the base change of `toBase0 N₀ p` to $\kappa$ along the identity are isomorphic (the type of isomorphisms is nonempty): first, the `rigidify` along `rigSection` of that base change with the section induced by $\varepsilon_0$, applied to the successive pullbacks — along `curveChange` of the component morphism of index $1$, along the comparison map `BaseChange.κ`, and along `baseChangeSnd` of $\psi_{\mathrm{red}}$ — of the `rigidify` along `rigSection` with $\mathfrak{P}.\varepsilon_{\inf}$ of the iterated tensor product over $i$ of $(\mathcal{I}_i^{\mathrm{pos}_i})^{\vee}$-module and $\mathcal{I}_i^{\mathrm{neg}_i}$-module, where $\mathcal{I}_i$ is the ideal sheaf of the graph of $s_i$ as a relative effective Cartier divisor on the pullback of `toBase N₀ p` along `Spec.map ρ`; second, the same $\varepsilon_0$-rigidification applied to the iterated tensor product formed in the same way from the graphs of the $z_i$, keeping only those indices $i$ with $c_i = 1$ and discarding the others.
--
--   This is the comparison, on the special fibre of the Deligne–Rapoport model, between a twist by divisors supported in the smooth locus and its restriction to one of the two components of the fibre: divisors whose special point lies on the chosen component contribute the corresponding point divisor on the level-$N_0$ curve over the residue field, while those meeting only the other component contribute nothing. It is used in the identifications of the abelian-quotient reading of the rigidified twist on the special fibre and in the comparison of the Poincaré bundle pulled back along that reading with the point twist.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_nonempty_rigidify_pullbackCurve_comp1_sectionTwist_iso.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve IsLocalRing ModularCurve ModularCurve.DRLevel

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem ModularCurve.DRModelPackageLevel.nonempty_rigidify_pullbackCurve_comp1_sectionTwist_iso
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := instDecidableEqResidueFieldSemistable A
    letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
    haveI : IsProper (toBase N₀ p) := 𝔓.isProper
    ∀ [IsProper (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))]
      (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase0 N₀ p))
      {n : ℕ} (s : Fin n → SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
      (_ : ∀ i, Set.range (s i).1.base ⊆ (𝔓.smoothLocus : Set (X N₀ p)))
      (c : Fin n → Fin 2)

      (y : Fin n → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A))))
      (_ : ∀ i, y i ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ (s i).1)
      (_ : ∀ i, y i ≫ pullback.snd _ _ = 𝟙 _)

      (z : Fin n → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ pullback (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A))))
      (hz : ∀ i, z i ≫ baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A) = 𝟙 _)
      (_ : ∀ i, z i ≫ 𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (c i) = y i)
      (_ : ∀ i, (y i).base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (1 - c i)).base)

      (ψred : SchemeHomOver (𝟙 _ ≫ specMap (R p) (ResidueField ↥A)) (Spec.map (CommRingCat.ofHom ρ)))
      (_ : ψred.1 = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
      (pos neg : Fin n → ℕ),
      Nonempty ((Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 _) (sectionBaseChange (ResidueField ↥A) ε₀))
          (pullback.snd (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 _)) ((Scheme.Modules.pullback (curveChange (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1) (𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1) (𝟙 _))).obj
        ((Scheme.Modules.pullback (BaseChange.κ (toBase N₀ p) (ResidueField ↥A) (𝟙 _)).hom).obj
          ((Scheme.Modules.pullback (baseChangeSnd (toBase N₀ p) ψred)).obj
            (Scheme.Modules.rigidify (rigSection (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ)) 𝔓.εinf)
            (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))) ((List.finRange n).foldr
            (fun i M => ((RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I ^ (pos i)).invModule ⊗
              ((RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I ^ (neg i)).module ⊗ M)
            (𝟙_ (pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))).Modules))))))) ≅
        (Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 _) (sectionBaseChange (ResidueField ↥A) ε₀))
          (pullback.snd (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 _)) ((List.finRange n).foldr
          (fun i M => if c i = 1 then
            ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I ^ (pos i)).invModule ⊗
              ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I ^ (neg i)).module ⊗ M
            else M)
          (𝟙_ _)))) := by sorry
