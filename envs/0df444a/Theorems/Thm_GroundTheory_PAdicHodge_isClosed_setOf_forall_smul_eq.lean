-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_isClosed_setOf_forall_smul_eq
-- name    : GroundTheory.PAdicHodge.isClosed_setOf_forall_smul_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:47:11.076443+00:00
-- url     : https://prove2.me/theorems/3ef8bca3-d718-4ff1-ba28-33e6eb573d95
-- title:
--   PAdic Hodge: is Closed set Of forall smul eq
-- statement:
--   The PAdic Hodge construction uses the is Closed set Of forall smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L465-L470
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L465-L470

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
noncomputable section
open UniformSpace Topology
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem GroundTheory.PAdicHodge.isClosed_setOf_forall_smul_eq (S : Set Gal(PadicAlgCl p/K)) :
    IsClosed {x : ℂ_[p] | ∀ σ ∈ S, σ • x = x} := by sorry
