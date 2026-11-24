-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_RatProj_exists_rat_proj
-- name    : GlobalTheory.MinorFrame.RatProj.exists_rat_proj
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:06:35.456034+00:00
-- url     : https://prove2.me/theorems/374e433d-b329-4c86-81bb-0f4e8ac50ef2
-- title:
--   Rat Proj: exists rat proj
-- statement:
--   The Rat Proj construction uses the exists rat proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsRationalFockProjectionMaximalMinors.lean#L83-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsRationalFockProjectionMaximalMinors.lean#L83-L116

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsRationalFockProjectionMaximalMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MeasureTheory
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.MinorFrame GlobalTheory.MinorFrame.RatProj
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.MinorFrame.RatProj.exists_rat_proj : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (k : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
  ∃ (M : ℕ) (r : Fin M → ℚ) (U : Fin M → GlobalTheory.MinorFrame.Tup ι a d n), ∀ T : GlobalTheory.MinorFrame.Tup ι a d n,
    Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.prodMinors T)
      (MvPolynomial.monomial k 1 - ∑ p, ((r p : ℚ) : ℂ) • GlobalTheory.MinorFrame.prodMinors (U p)) = 0 := by sorry
