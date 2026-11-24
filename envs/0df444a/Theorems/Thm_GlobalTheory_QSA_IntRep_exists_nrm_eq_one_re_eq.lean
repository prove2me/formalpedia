-- Prove2me | Theorems.Thm_GlobalTheory_QSA_IntRep_exists_nrm_eq_one_re_eq
-- name    : GlobalTheory.QSA.IntRep.exists_nrm_eq_one_re_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:23:00.216118+00:00
-- url     : https://prove2.me/theorems/670f3a4f-7264-4883-a286-8455b1af674e
-- title:
--   Int Rep: exists nrm eq one re eq
-- statement:
--   The Int Rep construction uses the exists nrm eq one re eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EventuallyExistsQuaternionNormOneReEq.lean#L133-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EventuallyExistsQuaternionNormOneReEq.lean#L133-L198

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsEqAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EventuallyExistsQuaternionNormOneReEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
open GlobalTheory GlobalTheory.QSA GlobalTheory.QSA.IntRep
open NumberField IsDedekindDomain
open scoped Quaternion Topology

theorem GlobalTheory.QSA.IntRep.exists_nrm_eq_one_re_eq : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 →
    ∀ᶠ v in (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))), ∀ t ∈ v.adicCompletionIntegers F,
      ∃ u : ℍ[v.adicCompletion F, algebraMap F (v.adicCompletion F) a, algebraMap F (v.adicCompletion F) b],
        _root_.GlobalTheory.QSA.nrm u = 1 ∧ u.re = t ∧ u.imI ∈ v.adicCompletionIntegers F ∧ u.imJ ∈ v.adicCompletionIntegers F ∧
          u.imK ∈ v.adicCompletionIntegers F := by sorry
