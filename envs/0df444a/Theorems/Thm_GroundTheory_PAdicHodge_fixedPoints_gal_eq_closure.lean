-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_fixedPoints_gal_eq_closure
-- name    : GroundTheory.PAdicHodge.fixedPoints_gal_eq_closure
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:46:37.807153+00:00
-- url     : https://prove2.me/theorems/3466a386-7e39-47c0-be14-76d2947e2c26
-- title:
--   PAdic Hodge: fixed Points gal eq closure
-- statement:
--   The PAdic Hodge construction uses the fixed Points gal eq closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L507-L515
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L507-L515

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

theorem GroundTheory.PAdicHodge.fixedPoints_gal_eq_closure :
    MulAction.fixedPoints Gal(PadicAlgCl p/K) ℂ_[p] =
      closure (((↑) : PadicAlgCl p → ℂ_[p]) '' (K : Set (PadicAlgCl p))) := by sorry
