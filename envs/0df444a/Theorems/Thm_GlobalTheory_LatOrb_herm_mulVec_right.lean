-- Prove2me | Theorems.Thm_GlobalTheory_LatOrb_herm_mulVec_right
-- name    : GlobalTheory.LatOrb.herm_mulVec_right
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:58:41.560278+00:00
-- url     : https://prove2.me/theorems/217b7741-658e-42cf-8bd5-0a9c961a8d46
-- title:
--   Lat Orb: herm mul Vec right
-- statement:
--   The Lat Orb construction uses the herm mul Vec right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSelfDualImageStandardLatticeUnitary.lean#L8-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSelfDualImageStandardLatticeUnitary.lean#L8-L15

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSelfDualImageStandardLatticeUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
open GlobalTheory GlobalTheory.LatOrb

theorem GlobalTheory.LatOrb.herm_mulVec_right {K : Type} [Field K] (σ : K →+* K)
    {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (y u : Fin n → K) :
    herm σ y (g *ᵥ u) = herm σ ((g.map σ)ᵀ *ᵥ y) u := by sorry
