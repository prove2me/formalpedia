-- Prove2me | Theorems.Thm_GlobalTheory_LemmaTwoFortyThirteen_main
-- name    : GlobalTheory.LemmaTwoFortyThirteen.main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:38.252799+00:00
-- url     : https://prove2.me/theorems/e7202c5d-ba8e-466b-9930-19ece5a51548
-- title:
--   Lemma Two Forty Thirteen: main
-- statement:
--   The Lemma Two Forty Thirteen construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ImportsAlt.lean#L5-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ImportsAlt.lean#L5-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ImportsAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LemmaTwoFortyThirteen

theorem GlobalTheory.LemmaTwoFortyThirteen.main {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (M : Submodule R V) (h : ∀ v : V, ∃ a : R, a ≠ (0 : R) ∧ a • v ∈ M) :
    Submodule.span K (↑M : Set V) = ⊤ := by sorry
