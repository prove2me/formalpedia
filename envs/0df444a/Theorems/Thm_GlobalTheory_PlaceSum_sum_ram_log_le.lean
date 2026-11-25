-- Prove2me | Theorems.Thm_GlobalTheory_PlaceSum_sum_ram_log_le
-- name    : GlobalTheory.PlaceSum.sum_ram_log_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:50:05.292+00:00
-- url     : https://prove2.me/theorems/1cea0aaa-4bd8-48bb-91cc-e58ad0f072e9
-- title:
--   Place Sum: sum ram log le
-- statement:
--   The Place Sum construction uses the sum ram log le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumFinitePlacesLeSumOverPrimes.lean#L43-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumFinitePlacesLeSumOverPrimes.lean#L43-L69

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
set_option linter.deprecated false

theorem GlobalTheory.PlaceSum.sum_ram_log_le {p : ℕ} (hp : p.Prime) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ la ∈ T, resCharOf la = p) :
    ∑ la ∈ T, (ramOverZ la : ℝ) * Real.log (Ideal.absNorm la.asIdeal) ≤
      (Module.finrank ℚ K : ℝ) * Real.log p := by sorry
