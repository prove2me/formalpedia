-- Prove2me | Theorems.Thm_GlobalTheory_JointHarm_fock_monomial_left
-- name    : GlobalTheory.JointHarm.fock_monomial_left
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:26:46.916605+00:00
-- url     : https://prove2.me/theorems/793ba65d-5e44-4885-a10d-ea5fe1da01fa
-- title:
--   Joint Harm: fock monomial left
-- statement:
--   The Joint Harm construction uses the fock monomial left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JointHarmonicOfHookNorm.lean#L42-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JointHarmonicOfHookNorm.lean#L42-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LowerUnipotentMinors
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JointHarmonicOfHookNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.JointHarm
open MvPolynomial Matrix GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionPolynomials
variable {n p q : ℕ}
open Formalism.E

theorem GlobalTheory.JointHarm.fock_monomial_left {σ : Type} (α : σ →₀ ℕ) (c : ℂ) (Q : MvPolynomial σ ℂ) :
    fock (monomial α c) Q = c * star (Q.coeff α) * (Formalism.A.mfact α : ℂ) := by sorry
