-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_section_generic_eq_pointEquivPlace_symm_of_forall_inertia_smul_eq
-- name    : ModularCurve.DRModelPackageLevel.exists_section_generic_eq_pointEquivPlace_symm_of_forall_inertia_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/9eb22a16-f77c-5288-a74e-f1b4e4f8cde5
-- title:
--   Inertia-fixed places give sections over the inertia valuation ring
-- statement:
--   Fix $N_0\ge 1$ and a prime $q$ with $q\nmid N_0$, and let $\mathfrak P$ be a level-$N_0q$ Deligne–Rapoport package `DRModelPackageLevel N₀ q hqN`, so that in particular the Igusa-type scheme `X N₀ q` is proper and flat over $\operatorname{Spec}$ of the ring `DRLevel.R q`, and $\mathfrak P$ carries a curve model $\mathfrak P.\mathrm{Meta}$ over $\overline{\mathbf Q}$ with function field `modularFunctionFieldBar (N₀ * q)` together with an isomorphism $\mathfrak P.\mathrm{eeta}$ from its underlying scheme onto the base change of `X N₀ q` to $\overline{\mathbf Q}$. Let $A$ be a valuation subring of $\overline{\mathbf Q}$, let $I_A$ denote `A.inertiaSubgroupIn ℚ`, the image in $\operatorname{Aut}(\overline{\mathbf Q}/\mathbf Q)$ of the inertia subgroup of $A$ inside its decomposition subgroup, and let $F$ be the fixed field of $I_A$. Let $O$ be a commutative ring together with a ring isomorphism $e_O$ of $O$ onto the valuation subring $A\cap F$ of $F$ (the comap of $A$ along $F\hookrightarrow\overline{\mathbf Q}$), and let $\rho_O\colon {}$`DRLevel.R q`$\to O$ be a ring homomorphism such that $\rho_O$ followed by $e_O$, the inclusion $A\cap F\hookrightarrow F$ and $F\hookrightarrow\overline{\mathbf Q}$ is the structure map `DRLevel.R q` $\to\overline{\mathbf Q}$. Let $V$ be a place of `modularFunctionFieldBar (N₀ * q)` over $\overline{\mathbf Q}$, that is, a proper valuation subring containing the image of $\overline{\mathbf Q}$ and whose valuation ring is a principal ideal ring, and assume $V$ is fixed by the semilinear action of `arithmeticGalois (modularFunctionFieldFull (N₀ * q))` $\sigma$ for every $\sigma\in I_A$. Then there exists a morphism $s$ from $\operatorname{Spec}O$ to the fibre product of `DRLevel.toBase N₀ q` with $\operatorname{Spec}\rho_O$ such that $s$ followed by the second projection is the identity on $\operatorname{Spec}O$, and such that $\operatorname{Spec}$ of the above ring map $O\to\overline{\mathbf Q}$, followed by $s$ and then by the first projection to `X N₀ q`, coincides with the $\overline{\mathbf Q}$-point of $\mathfrak P.\mathrm{Meta}$ corresponding to $V$ under the point–place bijection `pointEquivPlace`, followed by $\mathfrak P.\mathrm{eeta}$ and the first projection from the base change of `X N₀ q` to $\overline{\mathbf Q}$.
--
--   This is the extension step supplied by the valuative criterion of properness for the Deligne–Rapoport model at level $N_0q$: a place of the geometric function field that is fixed by the inertia group of $A$ spreads out from its $\overline{\mathbf Q}$-point to a section over the valuation ring of the inertia field. It is used in the later analysis of the special fibre at $q$, namely in the identification of node coordinates and chain positions of specialised places and in the computation of multidegrees in terms of branch depth.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_section_generic_eq_pointEquivPlace_symm_of_forall_inertia_smul_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_NodeDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve
open IsLocalRing

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.exists_section_generic_eq_pointEquivPlace_symm_of_forall_inertia_smul_eq
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    {A : ValuationSubring (AlgebraicClosure ℚ)}

    (O : Type) [CommRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (ρO : DRLevel.R q →+* O)
    (hρO : ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
        (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom))).comp ρO =
      algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))

    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)))
    (hV : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • V = V) :
    ∃ s : Spec (CommRingCat.of O) ⟶ pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)),
      s ≫ pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
          (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ s ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) =
        ((𝔓.Meta.pointEquivPlace).symm (V)).1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ q) _ := by sorry
