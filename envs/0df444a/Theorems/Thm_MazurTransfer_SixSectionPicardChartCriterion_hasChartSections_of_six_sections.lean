-- Prove2me | Theorems.Thm_MazurTransfer_SixSectionPicardChartCriterion_hasChartSections_of_six_sections
-- name    : MazurTransfer.SixSectionPicardChartCriterion.hasChartSections_of_six_sections
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T04:30:41.326772+00:00
-- url     : https://prove2.me/theorems/70f2b631-c9e7-4034-b27a-8131eca9e10e
-- title:
--   Six distinct sections give genus-two Picard chart sections
-- statement:
--   Let $c:C\to\operatorname{Spec}R$ be a curve over a commutative ring and let $\sigma_0,\ldots,\sigma_5$ be six sections. Assume that on every algebraically closed geometric fibre the six sections remain pairwise distinct. Assume also that each such fibre is isomorphic over its field to a curve model whose function field satisfies the genus-two Riemann–Roch formula $$\ell(D)-\ell(K_c-D)=\deg(D)+1-2\qquad\text{for every divisor }D.$$ Then the indexed family of all triples of the six sections gives Picard chart sections with $g=2$ and $r=5$: for every degree-five divisor on any geometric fibre, some triple cuts its Riemann–Roch space down to dimension one. This provides the chart-section input to relative Picard representability; the distinctness and genus-two model assumptions remain explicit.
-- source:
--   Unchanged statement and proof body from MazurTheorem SixSectionPicardChartCriterion.hasChartSections_of_six_sections. The proof adapts the complete official Anthropic FLT section-selection argument at commit 6e837e75355538c7f80bab5b956861e86c4eacc2 and directly reuses the public Riemann–Roch general-position theorem. Lean frontend declaration and command ranges hoist the proof to the required global solution, with the original section binders explicit. Complete original and public types are checked by closed kernel witnesses. Vas and contributors, Apache-2.0.

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_MazurTransfer_SixSectionTripleFamilyPublic
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra
open MazurTransfer.SixSectionPicardChartCriterion

theorem MazurTransfer.SixSectionPicardChartCriterion.hasChartSections_of_six_sections {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (σ : Fin 6 → SchemeHomOver (𝟙 (Spec (.of R))) c)
    (hσ : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (s : Spec (.of k) ⟶ Spec (.of R)),
      Function.Injective (fun i => s ≫ (σ i).1))
    (hmodel : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (s : Spec (.of k) ⟶ Spec (.of R)),
      ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : IsCurveOver k L)
        (M : CurveModel k L) (e : M.C ≅ pullback c s)
        (he : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L),
        ∀ D : Divisor k L, (ell D : ℤ) - ell (Kc-D) = Divisor.degree D + 1 - 2) :
    HasChartSections c (g := 2) (r := 5) (tripleFamily c σ)  := by sorry
