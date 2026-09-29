-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_bijective_algebraMap_sections_baseChange
-- name    : ModularCurve.XHDRModelAtP.bijective_algebraMap_sections_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/1428b6bc-e96b-5f34-b068-cc269765a209
-- title:
--   H⁰ of every base change of the model at p is A
-- statement:
--   Fix natural numbers $p$ and $M$ with $p$ prime and $M \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and assume $p \mid M$ and $p^2 \nmid M$; assume further that the Laurent series $j$-expansion `jqModC` over $\mathbb{Q}$ lies in the intermediate field `qExpFunctionFieldC` $\mathbb{Q}\,\top$ of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the integral form ratios for the full group $SL(2,\mathbb{Z})$. Let $\mathfrak{X}$ be a term of the structure `XHDRModelAtP p M H hpM hj`, the bundle of data for the integral model at $p$ of the modular curve of level $\Gamma_H(M)$: it records properness, flatness, integrality and local finite presentation of the structure morphism `toBase p (ΓM M H) hj` from the two-chart integral model over the ring `R p` with function field `qExpFunctionFieldC ℚ (ΓM M H)` and $j$-coordinate `jAt`, integral closedness of the sections over every affine open, properness and relative-dimension-one smoothness of the auxiliary $\Gamma_N$-level morphism, a `CurveModel` over an algebraic closure of $\mathbb{Q}$ isomorphic over the base to the generic geometric fibre together with its Galois equivariance and the pinning of the finite chart on $q$-expansions, and generic smoothness and geometric integrality. The conclusion: for every commutative ring $A$ carrying an `R p`-algebra structure, the canonical ring map from $A$ to the global sections $\Gamma(\mathcal{O})$ of the fibre product of `toBase p (ΓM M H) hj` with $\operatorname{Spec} A \to \operatorname{Spec}(\mathtt{R p})$, the $A$-algebra structure being the one induced by the second projection, is bijective.
--
--   This is the statement that the integral model of $X_H(M)$ at $p$ has $H^0(\mathcal{O}) = A$ after arbitrary base change along $\mathtt{R p} \to A$, i.e. that the model is cohomologically connected over its base in the strongest (universal) sense required for relative Picard functor arguments. It is one of the hypotheses consumed by the construction of the relative sub-Picard representation `exists_representsRelSubPic_algEquivZeroCut_epsInf_of_atkinLehner_generic_of_ker_le`, and is also used in `exists_forall_finrank_H1_fibre_eq`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_bijective_algebraMap_sections_baseChange.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.bijective_algebraMap_sections_baseChange
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj) :
    ∀ (A : Type) [CommRing A] [Algebra (R p) A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd (toBase p (ΓM M H) hj) (Scheme.TwoAffineOpenCover.specMap (R p) A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback (toBase p (ΓM M H) hj) (Scheme.TwoAffineOpenCover.specMap (R p) A), ⊤)) := by sorry
