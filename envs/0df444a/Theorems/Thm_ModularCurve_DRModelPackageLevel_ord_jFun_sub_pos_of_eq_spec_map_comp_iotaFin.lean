-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_ord_jFun_sub_pos_of_eq_spec_map_comp_iotaFin
-- name    : ModularCurve.DRModelPackageLevel.ord_jFun_sub_pos_of_eq_spec_map_comp_iotaFin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/326c06e0-cdb0-5a00-9088-301e15102b94
-- title:
--   Positivity of ord_W(j-φ(j)) for a chart A-point
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0 \neq 0$, $p$ prime and $p \nmid N_0$, and let $\mathfrak P$ be a Deligne–Rapoport model package `DRModelPackageLevel N₀ p hpN₀` for the Igusa scheme `X N₀ p` over $\operatorname{Spec}(R_p)$. Let $A$ be a valuation subring of $\overline{\mathbf Q}$. Let $y$ be a $\overline{\mathbf Q}$-point of the generic-fibre curve model $\mathfrak P.\mathrm{Meta}$, that is, a morphism $\operatorname{Spec}\overline{\mathbf Q} \to \mathfrak P.\mathrm{Meta}.C$ which is a section of $\mathfrak P.\mathrm{Meta}.\mathrm{toBase}$; write $W = \mathfrak P.\mathrm{Meta}.\mathrm{pointEquivPlace}\,y$ for the corresponding place of the function field $\mathrm{modularFunctionFieldBar}(N_0 p)$ over $\overline{\mathbf Q}$. Let $f \colon \operatorname{Spec} A \to$ `X N₀ p` be a morphism subject to two hypotheses: first, precomposing $f$ with the morphism $\operatorname{Spec}\overline{\mathbf Q} \to \operatorname{Spec} A$ induced by the inclusion $A \hookrightarrow \overline{\mathbf Q}$ gives the same morphism as $y$ followed by the isomorphism $\mathfrak P.\mathrm{eeta}$ onto the pullback of `toBase N₀ p` along $\operatorname{Spec}$ of $R_p \to \overline{\mathbf Q}$ and then the first projection; second, $f$ factors as $\operatorname{Spec}$ of a ring homomorphism $\varphi \colon \mathrm{chartAlgFin}(N_0 p, p) \to A$ followed by the chart immersion $\iota_{\mathrm{Fin}}(N_0 p, p)$. Then the order of vanishing of $\mathrm{jFun}(N_0,p) - \varphi(\mathrm{jChartFin}(N_0 p, p))$ at $W$ is strictly positive, where $\mathrm{jFun}(N_0,p)$ is the coefficientwise image of the $q$-expansion of $j$ in $\mathrm{modularFunctionFieldBar}(N_0 p)$ and the second term is the image of the element $\varphi(\mathrm{jChartFin}(N_0 p, p)) \in A \subseteq \overline{\mathbf Q}$ under the structure map of the function field.
--
--   This is the evaluation dictionary for the $j$-line chart of the Deligne–Rapoport model: an $A$-valued point landing in the $j$-finite affine chart has $j(W) = \varphi(j) \in A$ at the place $W$ attached to its generic point, so that $j$ minus that value vanishes there. It is used in [`ModularCurve.DRModelPackageLevel.reduceFst_mem_ssPlaces_of_specialPoint_eq_crossing`](thm.html#ModularCurve.DRModelPackageLevel.reduceFst_mem_ssPlaces_of_specialPoint_eq_crossing), where places whose closure meets a crossing of the special fibre are shown to reduce to supersingular points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_ord_jFun_sub_pos_of_eq_spec_map_comp_iotaFin.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_CharPReduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.DRLevel
  ModularCurve.IgusaScheme ModularCurve.PlaceSpecialization

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem ModularCurve.DRModelPackageLevel.ord_jFun_sub_pos_of_eq_spec_map_comp_iotaFin
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (f : Spec (CommRingCat.of ↥A) ⟶ X N₀ p)
    (hu : barPt A ≫ f = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
    (φ : ↥(chartAlgFin (N₀ * p) p) →+* ↥A) (hf : f = Spec.map (CommRingCat.ofHom φ) ≫ ιFin (N₀ * p) p) :
    0 < (𝔓.Meta.pointEquivPlace y).ord
      (ProlongationTuple.jFun N₀ p -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))
          ((φ (jChartFin (N₀ * p) p) : ↥A) : AlgebraicClosure ℚ)) := by sorry
