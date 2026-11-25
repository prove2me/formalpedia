-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_candidate_borel_move_open_frames_baire
-- name    : GlobalTheory.T.exists_candidate_borel_move_open_frames_baire
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:41.167897+00:00
-- url     : https://prove2.me/theorems/64430de5-c645-4dee-bd19-3474357f5b2a
-- title:
--   T: exists candidate borel move open frames baire
-- statement:
--   The T construction uses the exists candidate borel move open frames baire property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCandidateBorelMoveOpenFramesBaireStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCandidateBorelMoveOpenFramesBaireStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCandidateBorelMoveOpenFramesBaire
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCandidateBorelMoveOpenFramesBaireStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_candidate_borel_move_open_frames_baire : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (S : Set (GL (Fin r) E)) (a c : GL (Fin r) E) (W : Set (Frame X.Ψ r)), IsOpen W → W.Nonempty → W ⊆ X.dom → (∀ z ∈ W, ∃ γ ∈ S, ∃ b ∈ Bor X.Ψ r, lact c z = rmul (lact γ (lact a z)) b) → ∃ γ ∈ S, ∃ V : Set (Frame X.Ψ r), IsOpen V ∧ V.Nonempty ∧ V ⊆ X.dom ∧ ∀ x ∈ V, ∃ b ∈ Bor X.Ψ r, lact ((γ * a)⁻¹ * c) x = rmul x b := by sorry
