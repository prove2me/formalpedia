-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_natCast_notMem_of_not_dvd
-- name    : GroundTheory.Global.Cyclotomic.natCast_notMem_of_not_dvd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:37:32.203471+00:00
-- url     : https://prove2.me/theorems/d94fb46f-e42d-440a-bd23-850ac7f301b5
-- title:
--   Cyclotomic: nat Cast not Mem of not dvd
-- statement:
--   The Cyclotomic construction uses the nat Cast not Mem of not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Frobenius.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Frobenius.lean#L38-L43

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
variable {m : ℕ} [NeZero m] (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {m} ℚ K]
variable (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
omit [NeZero m] hp [NumberField K] [IsCyclotomicExtension {m} ℚ K] [P.IsPrime]

theorem GroundTheory.Global.Cyclotomic.natCast_notMem_of_not_dvd (hm : ¬ p ∣ m) : ((m : ℕ) : 𝓞 K) ∉ P := by sorry
