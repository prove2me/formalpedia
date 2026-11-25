-- Prove2me | Theorems.Thm_GlobalTheory_ofFn_prod_intertwine
-- name    : GlobalTheory.ofFn_prod_intertwine
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:02:34.872477+00:00
-- url     : https://prove2.me/theorems/e0582a3f-8e8c-4136-9aab-6f02aa3c87df
-- title:
--   Global Theory: of Fn prod intertwine
-- statement:
--   The Global Theory construction uses the of Fn prod intertwine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/QminorIntertwiningApply.lean#L6-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/QminorIntertwiningApply.lean#L6-L16

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QminorIntertwiningApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
open GlobalTheory

theorem GlobalTheory.ofFn_prod_intertwine {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ι : W →ₗ[ℂ] V) : ∀ (t : ℕ) (f : Fin t → Module.End ℂ V)
    (g : Fin t → Module.End ℂ W), (∀ k w, ι (g k w) = f k (ι w)) →
    ∀ w, ι ((List.ofFn g).prod w) = (List.ofFn f).prod (ι w) := by sorry
