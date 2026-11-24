-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_fixedPoints_gal_eq
-- name    : GroundTheory.PAdicHodge.fixedPoints_gal_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:46:20.477952+00:00
-- url     : https://prove2.me/theorems/ac4398af-0655-4c0e-8589-b3eb21c97053
-- title:
--   PAdic Hodge: fixed Points gal eq
-- statement:
--   The PAdic Hodge construction uses the fixed Points gal eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L525-L528
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L525-L528

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

theorem GroundTheory.PAdicHodge.fixedPoints_gal_eq [FiniteDimensional ℚ_[p] K] :
    MulAction.fixedPoints Gal(PadicAlgCl p/K) ℂ_[p] =
      ((↑) : PadicAlgCl p → ℂ_[p]) '' (K : Set (PadicAlgCl p)) := by sorry
