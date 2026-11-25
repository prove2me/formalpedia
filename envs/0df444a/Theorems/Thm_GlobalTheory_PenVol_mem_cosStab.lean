-- Prove2me | Theorems.Thm_GlobalTheory_PenVol_mem_cosStab
-- name    : GlobalTheory.PenVol.mem_cosStab
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:37.231899+00:00
-- url     : https://prove2.me/theorems/f6915dd1-2ef0-4b63-83ba-6d0142ae729b
-- title:
--   Pen Vol: mem cos Stab
-- statement:
--   The Pen Vol construction uses the mem cos Stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ToBlocksMulFinZero.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ToBlocksMulFinZero.lean#L38-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ToBlocksMulFinZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix ValuativeRel
open GlobalTheory GlobalTheory.PenVol
variable {k n : Type} [Field k] [ValuativeRel k] [Fintype n] [DecidableEq n]

theorem GlobalTheory.PenVol.mem_cosStab {J : Subgroup (GL (n ⊕ Fin 0) k)} {M : Submodule 𝒪[k] (n → k)} {c : (n → k) ⧸ M}
    {g : GL (n ⊕ Fin 0) k} : g ∈ cosStab J M c ↔ g ∈ J ∧ ∀ y : n → k,
      (Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y) : (n → k) ⧸ M) = c ↔ Submodule.Quotient.mk y = c := by sorry
