-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_map_commute_of_mem_genAlg
-- name    : GlobalTheory.RegSS.map_commute_of_mem_genAlg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T06:20:39.624815+00:00
-- url     : https://prove2.me/theorems/f743ae30-7420-561a-bd6e-b690f56c6403
-- title:
--   Reg SS: map commute of mem gen Alg
-- statement:
--   The Reg SS construction uses the map commute of mem gen Alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RegularSemisimpleTensorCommutant.lean#L48-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RegularSemisimpleTensorCommutant.lean#L48-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RegularSemisimpleTensorCommutant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem GlobalTheory.RegSS.map_commute_of_mem_genAlg {B : Type} [CommRing B] (f : A →+* B) {M l : Matrix n n A}
    {N : Matrix n n B} (h : N * M.map f = M.map f * N) (hl : l ∈ genAlg M) :
    N * l.map f = l.map f * N := by sorry
