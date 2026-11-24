-- Prove2me | Theorems.Thm_GlobalTheory_HomothetyLatSum_term_out_mulQ
-- name    : GlobalTheory.HomothetyLatSum.term_out_mulQ
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:37:38.508624+00:00
-- url     : https://prove2.me/theorems/736c96c5-d21b-4495-aea3-3e62395b3c1f
-- title:
--   Homothety Lat Sum: term out mul Q
-- statement:
--   The Homothety Lat Sum construction uses the term out mul Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomothetyLatSum.lean#L45-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomothetyLatSum.lean#L45-L52

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

theorem GlobalTheory.HomothetyLatSum.term_out_mulQ [IsCMField E] {φ : I → E →+* ℂ} (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) (α : E)
    (q : Quotient (unitRel (E := E))) :
    term φ (2 * s) κ σ (mulQ α q).out = term φ (2 * s) κ σ α * term φ (2 * s) κ σ q.out := by sorry
