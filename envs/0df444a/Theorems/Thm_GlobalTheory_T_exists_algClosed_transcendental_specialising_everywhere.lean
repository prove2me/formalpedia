-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_algClosed_transcendental_specialising_everywhere
-- name    : GlobalTheory.T.exists_algClosed_transcendental_specialising_everywhere
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:28:15.672986+00:00
-- url     : https://prove2.me/theorems/018f954a-2e69-5ad9-89a0-274558973c9f
-- title:
--   T: exists alg Closed transcendental specialising everywhere
-- statement:
--   The T construction uses the exists alg Closed transcendental specialising everywhere property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsAlgClosedTranscendentalSpecialisingEverywhStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsAlgClosedTranscendentalSpecialisingEverywhStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAlgClosedTranscendentalSpecialisingEverywh
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAlgClosedTranscendentalSpecialisingEverywhStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_algClosed_transcendental_specialising_everywhere : ∀ (K : Type) [Field K] [IsAlgClosed K], ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (ι : K →+* L) (s : L), (∀ P : Polynomial K, P.eval₂ ι s = 0 → P = 0) ∧ ∀ a : K, ∃ (V : ValuationSubring L) (ιV : K →+* V) (r : V →+* K) (sV : V), (algebraMap V L).comp ιV = ι ∧ r.comp ιV = RingHom.id K ∧ RingHom.ker r = IsLocalRing.maximalIdeal V ∧ algebraMap V L sV = s ∧ r sV = a := by sorry
