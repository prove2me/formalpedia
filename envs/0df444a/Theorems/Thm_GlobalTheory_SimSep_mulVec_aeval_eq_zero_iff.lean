-- Prove2me | Theorems.Thm_GlobalTheory_SimSep_mulVec_aeval_eq_zero_iff
-- name    : GlobalTheory.SimSep.mulVec_aeval_eq_zero_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:13:25.049142+00:00
-- url     : https://prove2.me/theorems/ef808e21-95b1-442e-bcc4-bab35edf7ba6
-- title:
--   Sim Sep: mul Vec aeval eq zero iff
-- statement:
--   The Sim Sep construction uses the mul Vec aeval eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConjOfCharpolyEqOfCharpolySeparable.lean#L7-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConjOfCharpolyEqOfCharpolySeparable.lean#L7-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCyclicVectorOfSeparableCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjOfCharpolyEqOfCharpolySeparable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory GlobalTheory.SimSep

theorem GlobalTheory.SimSep.mulVec_aeval_eq_zero_iff {R : Type} [Field R] {m : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (v : Fin m → R) (hv : ∀ u : Fin m → R, ∃ p : R[X], u = aeval A p *ᵥ v) (p : R[X]) :
    aeval A p *ᵥ v = 0 ↔ A.charpoly ∣ p := by sorry
