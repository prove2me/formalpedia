-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_eq_coe_of_forall_smul_eq
-- name    : GroundTheory.PAdicHodge.exists_eq_coe_of_forall_smul_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:57.978921+00:00
-- url     : https://prove2.me/theorems/997acb1f-3166-40c2-8dc8-27db6db5c922
-- title:
--   PAdic Hodge: exists eq coe of forall smul eq
-- statement:
--   The PAdic Hodge construction uses the exists eq coe of forall smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L530-L536
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L530-L536

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

theorem GroundTheory.PAdicHodge.exists_eq_coe_of_forall_smul_eq [FiniteDimensional ℚ_[p] K] {x : ℂ_[p]}
    (hx : ∀ σ : Gal(PadicAlgCl p/K), σ • x = x) :
    ∃ k : K, ((k : PadicAlgCl p) : ℂ_[p]) = x := by sorry
