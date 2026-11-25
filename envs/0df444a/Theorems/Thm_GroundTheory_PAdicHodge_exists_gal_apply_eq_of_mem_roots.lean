-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_gal_apply_eq_of_mem_roots
-- name    : GroundTheory.PAdicHodge.exists_gal_apply_eq_of_mem_roots
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:46:30.672986+00:00
-- url     : https://prove2.me/theorems/b36180e0-7566-47a2-bc57-3d6e504448cf
-- title:
--   PAdic Hodge: exists gal apply eq of mem roots
-- statement:
--   The PAdic Hodge construction uses the exists gal apply eq of mem roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L154-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L154-L164

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
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem GroundTheory.PAdicHodge.exists_gal_apply_eq_of_mem_roots {x a : PadicAlgCl p}
    (ha : a ∈ ((minpoly K x).map (algebraMap K (PadicAlgCl p))).roots) :
    ∃ σ : Gal(PadicAlgCl p/K), σ x = a := by sorry
