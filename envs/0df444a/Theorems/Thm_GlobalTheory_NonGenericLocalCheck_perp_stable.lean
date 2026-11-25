-- Prove2me | Theorems.Thm_GlobalTheory_NonGenericLocalCheck_perp_stable
-- name    : GlobalTheory.NonGenericLocalCheck.perp_stable
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:42:09.530831+00:00
-- url     : https://prove2.me/theorems/920b8dee-6fa7-4029-9d3e-7d86ba5ea6bc
-- title:
--   Non Generic Local Check: perp stable
-- statement:
--   The Non Generic Local Check construction uses the perp stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/TransversalityLocal/FramePairFixatorUnitaryAndFixesFrame.lean#L99-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/TransversalityLocal/FramePairFixatorUnitaryAndFixesFrame.lean#L99-L111

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_TransversalityLocal_FramePairFixatorUnitaryAndFixesFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
open GlobalTheory GlobalTheory.NonGenericLocalCheck
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E}
variable {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

theorem GlobalTheory.NonGenericLocalCheck.perp_stable {g : V ≃ₗ[E] V} (hu : IsUnitary H g) (f : Fin (r + 1) → V)
    (hf : ∀ b, g (f b) = f b) {v : V} (hv : v ∈ H.perp (H.X f)) : g v ∈ H.perp (H.X f) := by sorry
