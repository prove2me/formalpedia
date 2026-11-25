-- Prove2me | Theorems.Thm_GlobalTheory_FlagHook_Degree_flagDeg_eq_and_product
-- name    : GlobalTheory.FlagHook.Degree.flagDeg_eq_and_product
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:05:27.261387+00:00
-- url     : https://prove2.me/theorems/26a3a411-e4d0-47e3-ba45-c77b0fe103ac
-- title:
--   Degree: flag Deg eq and product
-- statement:
--   The Degree construction uses the flag Deg eq and product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlagDegreeVandermonde.lean#L92-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlagDegreeVandermonde.lean#L92-L97

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

theorem GlobalTheory.FlagHook.Degree.flagDeg_eq_and_product :
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (u : ι → Fin N → ℝ),
      flagDeg ι N u = ((dimFl ι N).factorial : ℝ) * ∏ τ, eval (u τ) (detE (rho N))) ∧
    ∀ (N : ℕ) (v : Fin N → ℝ), eval v (detE (rho N)) =
      (∏ a : Fin N, ∏ b ∈ Ioi a, (v a - v b)) / ∏ m ∈ range N, (m.factorial : ℝ) := by sorry
