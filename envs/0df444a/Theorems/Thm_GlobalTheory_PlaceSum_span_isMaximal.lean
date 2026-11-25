-- Prove2me | Theorems.Thm_GlobalTheory_PlaceSum_span_isMaximal
-- name    : GlobalTheory.PlaceSum.span_isMaximal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:21:20.360565+00:00
-- url     : https://prove2.me/theorems/c98a993e-5ef9-4557-8e53-105e9209cc17
-- title:
--   Place Sum: span is Maximal
-- statement:
--   The Place Sum construction uses the span is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumFinitePlacesLeSumOverPrimes.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumFinitePlacesLeSumOverPrimes.lean#L22-L24

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

theorem GlobalTheory.PlaceSum.span_isMaximal {p : ℕ} (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsMaximal := by sorry
