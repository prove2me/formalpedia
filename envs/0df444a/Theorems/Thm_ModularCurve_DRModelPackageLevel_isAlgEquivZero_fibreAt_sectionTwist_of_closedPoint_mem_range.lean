-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_isAlgEquivZero_fibreAt_sectionTwist_of_closedPoint_mem_range
-- name    : ModularCurve.DRModelPackageLevel.isAlgEquivZero_fibreAt_sectionTwist_of_closedPoint_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/06554f4d-1a9d-54f5-a889-035b13587968
-- title:
--   Bidegree-zero section twists are algebraically trivial on geometric fibres
-- statement:
--   Fix natural numbers $N_0 \neq 0$ and a prime $p$ with $p \nmid N_0$, and a package $\mathfrak{P} : \mathtt{DRModelPackageLevel}\,N_0\,p$ of data and properties for the structure morphism $\mathtt{toBase}\,N_0\,p = \mathtt{igusaTo}\,(N_0 p)\,p : X(N_0,p) \to \operatorname{Spec} R_p$ (properness, flatness, integrality, finite presentation, normality on affines, an identification of the geometric generic fibre with a curve model of the modular function field, and further data including the open set $\mathfrak{P}.\mathtt{smoothLocus}$ and the component morphisms $\mathfrak{P}.\mathtt{comp}$). Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, and let $\rho : R_p \to A$ be a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map $R_p \to \overline{\mathbb{Q}}$. Let $s_0,\dots,s_{n-1}$ be morphisms $\operatorname{Spec} A \to X(N_0,p)$ over $\operatorname{Spec}\rho$, each with topological image inside $\mathfrak{P}.\mathtt{smoothLocus}$. The residue field of $A$ then has characteristic $p$, and $\mathtt{toBase}\,N_0\,p$ is proper. Assert: for every labelling $c : \{0,\dots,n-1\} \to \{0,1\}$; for all morphisms $y_i : \operatorname{Spec} \kappa \to X(N_0,p) \times_{\operatorname{Spec} R_p} \operatorname{Spec}\kappa$ ($\kappa$ the residue field of $A$, the fibre product taken along $\mathtt{residue} \circ \rho$) which are sections of the second projection and whose first components are the reductions $\operatorname{Spec}\kappa \to \operatorname{Spec} A \xrightarrow{s_i} X(N_0,p)$, with the image of each $y_i$ contained in the image of $\mathfrak{P}.\mathtt{comp}$ at the index $c(i)$; for all multiplicities $\mathrm{pos}, \mathrm{neg} : \{0,\dots,n-1\} \to \mathbb{N}$ satisfying $\sum_{i : c(i) = j} (\mathrm{pos}(i) - \mathrm{neg}(i)) = 0$ in $\mathbb{Z}$ for $j = 0,1$; and for every algebraically closed field $k$ and morphism $s_k : \operatorname{Spec} k \to \operatorname{Spec} A$ whose image contains the closed point of $A$ — the pullback along $\mathtt{pullback.fst}$ to the geometric fibre $(X(N_0,p) \times_{\operatorname{Spec} R_p} \operatorname{Spec} A) \times_{\operatorname{Spec} A} \operatorname{Spec} k$ of the module $\bigotimes_i \big( (\mathcal{I}_{s_i}^{\mathrm{pos}(i)})^{\vee} \otimes \mathcal{I}_{s_i}^{\mathrm{neg}(i)} \big)$, formed by folding over $i$ from the unit module, where $\mathcal{I}_{s_i}$ is the ideal sheaf of the relative effective Cartier divisor of degree one cut out by the graph of $s_i$, satisfies $\mathtt{IsAlgEquivZero}$ for the projection $\mathtt{fibreAt}$ to $\operatorname{Spec} k$: there are a geometrically integral, locally of finite type $k$-scheme $T'$, an invertible module $M$ on the product of the geometric fibre with $T'$, and two $k$-sections $t_0, t_1$ of $T'$ such that the restriction of $M$ along $t_0$ is isomorphic to the unit sheaf and its restriction along $t_1$ is isomorphic to the given module.
--
--   This is the statement that a section twist of total degree zero on each of the two components of the special fibre of the Deligne–Rapoport model lies in the identity component of the relative Picard functor after passage to a geometric fibre over the closed point of $\operatorname{Spec} A$. It is used in the construction of a rigidified line bundle pulled back from the Poincaré bundle, namely in [`ModularCurve.DRModelPackageLevel.exists_schemeHomOver_poincare_pullbackAlong_iso_rigidify_sectionTwist_of_sum_eq_zero`](thm.html#ModularCurve.DRModelPackageLevel.exists_schemeHomOver_poincare_pullbackAlong_iso_rigidify_sectionTwist_of_sum_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_isAlgEquivZero_fibreAt_sectionTwist_of_closedPoint_mem_range.lean

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

theorem ModularCurve.DRModelPackageLevel.isAlgEquivZero_fibreAt_sectionTwist_of_closedPoint_mem_range
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    {n : ℕ} (s : Fin n → SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
    (hsm : ∀ i, Set.range (s i).1.base ⊆ (𝔓.smoothLocus : Set (X N₀ p))) :
    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := instDecidableEqResidueFieldSemistable A
    haveI : IsProper (toBase N₀ p) := 𝔓.isProper
    ∀ (c : Fin n → Fin 2)

      (y : Fin n → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue ↥A).comp ρ)))
      (_hy₁ : ∀ i, y i ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ (s i).1)
      (_hy₂ : ∀ i, y i ≫ pullback.snd _ _ = 𝟙 _)

      (_hc : ∀ i, Set.range (y i).base ⊆
        Set.range (𝔓.comp (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ) (c i)).base)

      (pos neg : Fin n → ℕ)
      (_hdeg : ∀ j : Fin 2, (∑ i ∈ Finset.univ.filter (fun i => c i = j), ((pos i : ℤ) - (neg i : ℤ))) = 0)
      (k : Type) [Field k] [IsAlgClosed k] (sk : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ↥A))
      (_hsp : IsLocalRing.closedPoint ↥A ∈ Set.range sk.base),
      IsAlgEquivZero (fibreAt (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ)) sk)
        ((Scheme.Modules.pullback (pullback.fst (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))) sk)).obj
          ((List.finRange n).foldr
            (fun i M => ((RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I ^ (pos i)).invModule ⊗
              ((RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I ^ (neg i)).module ⊗ M)
            (𝟙_ (pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))).Modules))) := by sorry
