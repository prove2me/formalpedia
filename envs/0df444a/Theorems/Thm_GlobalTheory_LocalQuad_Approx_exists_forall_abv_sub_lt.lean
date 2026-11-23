-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_Approx_exists_forall_abv_sub_lt
-- name    : GlobalTheory.LocalQuad.Approx.exists_forall_abv_sub_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:06.946116+00:00
-- url     : https://prove2.me/theorems/648f9471-02cd-4ddc-ab2f-d73753206225
-- title:
--   Approx: exists forall abv sub lt
-- statement:
--   The Approx construction uses the exists forall abv sub lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsForallAbvSubLt.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsForallAbvSubLt.lean#L11-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsForallAbvSubLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad GlobalTheory.LocalQuad.Approx
open NumberField IsDedekindDomain
open scoped Matrix WithZero

theorem GlobalTheory.LocalQuad.Approx.exists_forall_abv_sub_lt {F : Type*} [Field F] {ι : Type*} [Finite ι]
    {v : ι → AbsoluteValue F ℝ} (h : ∀ i, (v i).IsNontrivial)
    (hv : Pairwise fun i j ↦ ¬(v i).IsEquiv (v j)) (z : ι → F) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : F, ∀ i, v i (z i - x) < ε := by sorry
