-- Prove2me | Theorems.Thm_GlobalTheory_FlagHook_Degree_flagDeg_eq
-- name    : GlobalTheory.FlagHook.Degree.flagDeg_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:31:43.415801+00:00
-- url     : https://prove2.me/theorems/798eb8d1-0897-4d02-b5e8-ddeec3a4f251
-- title:
--   Degree: flag Deg eq
-- statement:
--   The Degree construction uses the flag Deg eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlagDegreeVandermonde.lean#L68-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlagDegreeVandermonde.lean#L68-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_AltCoeffRho
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagDegreeVandermonde
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula
noncomputable section
open GlobalTheory GlobalTheory.FlagHook GlobalTheory.FlagHook.Degree
variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

theorem GlobalTheory.FlagHook.Degree.flagDeg_eq (u : ι → Fin N → ℝ) :
    flagDeg ι N u = ((dimFl ι N).factorial : ℝ) * ∏ τ, eval (u τ) (detE (rho N)) := by sorry
