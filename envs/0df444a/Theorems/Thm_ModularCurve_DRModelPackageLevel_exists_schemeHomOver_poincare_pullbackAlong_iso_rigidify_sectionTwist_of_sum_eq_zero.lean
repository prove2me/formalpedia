-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_schemeHomOver_poincare_pullbackAlong_iso_rigidify_sectionTwist_of_sum_eq_zero
-- name    : ModularCurve.DRModelPackageLevel.exists_schemeHomOver_poincare_pullbackAlong_iso_rigidify_sectionTwist_of_sum_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/c361411c-045b-5c50-ad0e-e72abafb9e5c
-- title:
--   Bidegree-zero section twists give A-points of relative Pic⁰
-- statement:
--   Fix a nonzero $N_0$ and a prime $p$ with $p \nmid N_0$, and let $\mathfrak P$ be a `DRModelPackageLevel N₀ p hpN₀`, so the curve `X N₀ p` comes with the structure morphism `toBase N₀ p` to $\operatorname{Spec}$ of the base ring `R p`, which is proper, flat and locally of finite presentation with integral source, together with its two sections `εinf`, `εzero`, its identification of the geometric generic fibre with a curve model of the modular function field, and its open subset `𝔓.smoothLocus`. Let $D$ be a `RelativePic0Designation`, i.e. a scheme `D.P` over `R p` with a zero section, and let `hD` witness that $D$ represents, through a Poincaré rigidified line bundle `hD.poincare` on the product with `D.toBase` rigidified along `εinf`, the condition `algEquivZeroCut`: a rigidified invertible module on $\mathrm{X} \times_{R p} T$ qualifies exactly when for every algebraically closed field $k$ and every $k$-point of $T$ the restriction to the corresponding fibre is algebraically equivalent to zero. Let $A$ be a valuation subring of $\overline{\mathbf Q}$ with $p$ a nonunit of $A$, and $\rho : R p \to A$ a ring homomorphism compatible with the structure map $R p \to \overline{\mathbf Q}$. Let $s_0,\dots,s_{n-1}$ be sections $\operatorname{Spec} A \to \mathrm{X}$ over $\operatorname{Spec}\rho$ whose images lie in `𝔓.smoothLocus`. The assertion is then: for every labelling $c : \mathrm{Fin}\,n \to \mathrm{Fin}\,2$, every family $y_i$ of morphisms from $\operatorname{Spec}$ of the residue field of $A$ to the fibre of `toBase N₀ p` along the reduction $\operatorname{Spec}$ of $(\text{residue}) \circ \rho$ which are sections of the second projection and whose first projections are the reductions of the $s_i$, such that the image of $y_i$ lies in the image of the morphism `𝔓.comp (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ) (c i)` (the $c_i$-th of the two distinguished morphisms into the special fibre), and all $\mathrm{pos}, \mathrm{neg} : \mathrm{Fin}\,n \to \mathbf N$ satisfying $\sum_{c_i = j} (\mathrm{pos}_i - \mathrm{neg}_i) = 0$ for each $j \in \{0,1\}$, there exists a morphism $a : \operatorname{Spec} A \to D.P$ over $\operatorname{Spec} R p$ such that the underlying module of the pullback of `hD.poincare` along $a$ is isomorphic to the rigidification, along `rigSection` for `εinf` and the second projection, of the iterated tensor product over $i = 0,\dots,n-1$ of the dual of the $\mathrm{pos}_i$-th power of the ideal sheaf module of the relative effective Cartier divisor cut out by the graph of $s_i$ tensored with the $\mathrm{neg}_i$-th power of that ideal sheaf module, starting from the unit module.
--
--   This is the step which, given $A$-sections of the Deligne–Rapoport model of $X_0(N_0p)$ in the smooth locus whose associated divisor has degree zero on each of the two components of the special fibre, produces the corresponding $A$-valued point of the relative $\mathrm{Pic}^0$ and identifies the pullback of the Poincaré bundle with the rigidified twist. It feeds the analysis of the reduction of divisor classes and of which classes extend to places, used in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_schemeHomOver_poincare_pullbackAlong_iso_rigidify_sectionTwist_of_sum_eq_zero.lean

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

theorem ModularCurve.DRModelPackageLevel.exists_schemeHomOver_poincare_pullbackAlong_iso_rigidify_sectionTwist_of_sum_eq_zero
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)

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
      (_hdeg : ∀ j : Fin 2, (∑ i ∈ Finset.univ.filter (fun i => c i = j), ((pos i : ℤ) - (neg i : ℤ))) = 0),
    ∃ a : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
      Nonempty ((hD.poincare.pullbackAlong a).L ≅
        Scheme.Modules.rigidify (rigSection (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ)) 𝔓.εinf)
          (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ)))
          ((List.finRange n).foldr
            (fun i M => ((RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I ^ (pos i)).invModule ⊗
              ((RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I ^ (neg i)).module ⊗ M)
            (𝟙_ (pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))).Modules))) := by sorry
