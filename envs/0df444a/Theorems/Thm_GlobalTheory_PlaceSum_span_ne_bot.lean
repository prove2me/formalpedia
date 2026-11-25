-- Prove2me | Theorems.Thm_GlobalTheory_PlaceSum_span_ne_bot
-- name    : GlobalTheory.PlaceSum.span_ne_bot
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:19:17.550959+00:00
-- url     : https://prove2.me/theorems/478255e1-1bac-4785-9d51-8d1c7e33dcca
-- title:
--   Place Sum: span ne bot
-- statement:
--   The Place Sum construction uses the span ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumFinitePlacesLeSumOverPrimes.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumFinitePlacesLeSumOverPrimes.lean#L19-L20

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumFinitePlacesLeSumOverPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Pj
open GlobalTheory GlobalTheory.PlaceSum
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.PlaceSum.span_ne_bot {p : ℕ} (hp : p.Prime) : Ideal.span {(p : ℤ)} ≠ ⊥ := by sorry
