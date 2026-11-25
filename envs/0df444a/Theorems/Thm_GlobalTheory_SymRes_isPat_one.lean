-- Prove2me | Theorems.Thm_GlobalTheory_SymRes_isPat_one
-- name    : GlobalTheory.SymRes.isPat_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:25:46.153877+00:00
-- url     : https://prove2.me/theorems/78aa588a-4e3a-4d11-818d-60781b11eeda
-- title:
--   Sym Res: is Pat one
-- statement:
--   The Sym Res construction uses the is Pat one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IsPatOne.lean#L11-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IsPatOne.lean#L11-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsPatOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SymRes

theorem GlobalTheory.SymRes.isPat_one {K : Type} [CommRing K] {r : ℕ} (ρ κ : ℕ) : IsPat ρ κ (1 : GL (Fin r) K) := by sorry
