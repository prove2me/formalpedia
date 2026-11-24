-- Prove2me | Theorems.Thm_GlobalTheory_ColLie_hasDerivAt_coeff_colSub_exp
-- name    : GlobalTheory.ColLie.hasDerivAt_coeff_colSub_exp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:30:30.252995+00:00
-- url     : https://prove2.me/theorems/fa2daaa8-480d-4518-93bb-ed2542f03836
-- title:
--   Col Lie: has Deriv At coeff col Sub exp
-- statement:
--   The Col Lie construction uses the has Deriv At coeff col Sub exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasDerivAtCoeffFockColumnSubstitutionExp.lean#L93-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasDerivAtCoeffFockColumnSubstitutionExp.lean#L93-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColDerApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasDerivAtCoeffFockColumnSubstitutionExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.ColLie
open GlobalTheory.MinorFrame
variable {ι : Type} [DecidableEq ι]

theorem GlobalTheory.ColLie.hasDerivAt_coeff_colSub_exp {ι : Type} [Fintype ι] [DecidableEq ι] (d a : ℕ) (τ : ι)
    (S : Matrix (Fin a) (Fin a) ℂ) (R : Pol ι d a) (m : Var ι d a →₀ ℕ) :
    HasDerivAt (fun h : ℝ => coeff m (colSub (atPl τ (NormedSpace.exp ((h : ℂ) • S))) R))
      (coeff m (colDer τ S R)) 0 := by sorry
