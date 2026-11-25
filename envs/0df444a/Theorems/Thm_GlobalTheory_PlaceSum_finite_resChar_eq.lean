-- Prove2me | Theorems.Thm_GlobalTheory_PlaceSum_finite_resChar_eq
-- name    : GlobalTheory.PlaceSum.finite_resChar_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:49:45.144225+00:00
-- url     : https://prove2.me/theorems/69e05f0b-ac6e-4cee-88a2-7e67cad936aa
-- title:
--   Place Sum: finite res Char eq
-- statement:
--   The Place Sum construction uses the finite res Char eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumFinitePlacesLeSumOverPrimes.lean#L33-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumFinitePlacesLeSumOverPrimes.lean#L33-L39

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

theorem GlobalTheory.PlaceSum.finite_resChar_eq {p : ℕ} (hp : p.Prime) :
    {la : HeightOneSpectrum (𝓞 K) | resCharOf la = p}.Finite := by sorry
