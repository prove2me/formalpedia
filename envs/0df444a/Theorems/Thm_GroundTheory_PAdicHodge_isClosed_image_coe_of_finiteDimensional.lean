-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_isClosed_image_coe_of_finiteDimensional
-- name    : GroundTheory.PAdicHodge.isClosed_image_coe_of_finiteDimensional
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:46:50.124326+00:00
-- url     : https://prove2.me/theorems/9948ed13-1015-49a1-a513-d75dc7082890
-- title:
--   PAdic Hodge: is Closed image coe of finite Dimensional
-- statement:
--   The PAdic Hodge construction uses the is Closed image coe of finite Dimensional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L517-L523
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L517-L523

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

theorem GroundTheory.PAdicHodge.isClosed_image_coe_of_finiteDimensional [FiniteDimensional ℚ_[p] K] :
    IsClosed (((↑) : PadicAlgCl p → ℂ_[p]) '' (K : Set (PadicAlgCl p))) := by sorry
