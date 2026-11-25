-- Prove2me | Theorems.Thm_GlobalTheory_T_schroedingerOperatorHeisenberg_preserves_schwartzBruhat
-- name    : GlobalTheory.T.schroedingerOperatorHeisenberg_preserves_schwartzBruhat
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:42:36.215151+00:00
-- url     : https://prove2.me/theorems/d50a6b09-4860-4f93-880b-3e180d0e5c03
-- title:
--   T: schroedinger Operator Heisenberg preserves schwartz Bruhat
-- statement:
--   The T construction uses the schroedinger Operator Heisenberg preserves schwartz Bruhat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchroedingerOperatorHeisenbergPreservesSchwartzBStatement.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchroedingerOperatorHeisenbergPreservesSchwartzBStatement.lean#L10-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchroedingerOperatorHeisenbergPreservesSchwartzB
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchroedingerOperatorHeisenbergPreservesSchwartzBStatement
import Theorems.Thm_GlobalTheory_Adopt_schroedingerOperatorHeisenberg_preserves_schwartzBruhat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.schroedingerOperatorHeisenberg_preserves_schwartzBruhat : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    ∀ {κ : Type} [Fintype κ] (w : (κ → k) × (κ → k)), ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), GlobalTheory.WeilM.schr ψ0 w φ ∈ GlobalTheory.WeilM.SB (κ → k) := by sorry
