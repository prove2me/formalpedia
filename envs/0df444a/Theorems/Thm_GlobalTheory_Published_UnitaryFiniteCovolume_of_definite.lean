-- Prove2me | Theorems.Thm_GlobalTheory_Published_UnitaryFiniteCovolume_of_definite
-- name    : GlobalTheory.Published.UnitaryFiniteCovolume.of_definite
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:17:25.55526+00:00
-- url     : https://prove2.me/theorems/80420bad-cc12-5ef8-857f-f562f8176abf
-- title:
--   Unitary Finite Covolume: of definite
-- statement:
--   The Unitary Finite Covolume construction uses the of definite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/DefiniteCompactness/ExistsCompactOfDefinite.lean#L84-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/DefiniteCompactness/ExistsCompactOfDefinite.lean#L84-L96

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_DefiniteCompactness_ExistsCompactOfDefinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.UnitaryFiniteCovolume
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.Published.UnitaryFiniteCovolume.of_definite {r : ℕ} (X : Data E r) (hd : X.p0 = 0 ∨ X.p0 = r)
    (H : Subgroup (X.Ψ → GL (Fin r) ℂ))
    (hH : ∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ))
    [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure] :
    ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧
      ∀ g : H, ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∃ w ∈ Ω, ∀ τ : X.Ψ,
        (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
          (γ : Matrix (Fin r) (Fin r) E).map τ.1 *
            (((w : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by sorry
