-- Prove2me | Theorems.Thm_GlobalTheory_HomothetyLatSum_term_eq_lamInf
-- name    : GlobalTheory.HomothetyLatSum.term_eq_lamInf
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:37:49.904594+00:00
-- url     : https://prove2.me/theorems/27cf02a7-998c-419e-b7e8-3778cab8cfca
-- title:
--   Homothety Lat Sum: term eq lam Inf
-- statement:
--   The Homothety Lat Sum construction uses the term eq lam Inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomothetyLatSum.lean#L54-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomothetyLatSum.lean#L54-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdNormSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomothetyLatSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
open GlobalTheory GlobalTheory.HomothetyLatSum
variable {E : Type} [Field E] [NumberField E]
variable {I : Type} [Fintype I]

theorem GlobalTheory.HomothetyLatSum.term_eq_lamInf [IsCMField E] {φ : I → E →+* ℂ} (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) (α : Eˣ) :
    term φ (2 * s) κ σ α =
      (lamInf φ (2 * s) κ α)⁻¹ * ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-σ) := by sorry
