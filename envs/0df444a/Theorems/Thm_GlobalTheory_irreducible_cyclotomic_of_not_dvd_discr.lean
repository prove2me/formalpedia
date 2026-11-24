-- Prove2me | Theorems.Thm_GlobalTheory_irreducible_cyclotomic_of_not_dvd_discr
-- name    : GlobalTheory.irreducible_cyclotomic_of_not_dvd_discr
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:56:17.760798+00:00
-- url     : https://prove2.me/theorems/4467101c-2118-4375-b2cb-cb63ee702f05
-- title:
--   Global Theory: irreducible cyclotomic of not dvd discr
-- statement:
--   The Global Theory construction uses the irreducible cyclotomic of not dvd discr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPrimeDvdSubOneCyclotomicIrreducibleOver.lean#L18-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPrimeDvdSubOneCyclotomicIrreducibleOver.lean#L18-L86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimeDvdSubOneCyclotomicIrreducibleOver
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
open GlobalTheory

theorem GlobalTheory.irreducible_cyclotomic_of_not_dvd_discr (K : Type) [Field K] [NumberField K] (m : ℕ)
    (hm : m.Prime) (hd : ¬ (m : ℤ) ∣ discr K) : Irreducible (cyclotomic m K) := by sorry
