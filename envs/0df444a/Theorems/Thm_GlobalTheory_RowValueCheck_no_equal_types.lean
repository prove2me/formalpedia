-- Prove2me | Theorems.Thm_GlobalTheory_RowValueCheck_no_equal_types
-- name    : GlobalTheory.RowValueCheck.no_equal_types
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:26:43.574369+00:00
-- url     : https://prove2.me/theorems/4ada851a-f9d7-4d67-8a11-636b8c806d84
-- title:
--   Row Value Check: no equal types
-- statement:
--   The Row Value Check construction uses the no equal types property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/ValOfKindIndep.lean#L23-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/ValOfKindIndep.lean#L23-L40

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_ValOfKindIndep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open GlobalTheory GlobalTheory.RowValueCheck
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

theorem GlobalTheory.RowValueCheck.no_equal_types (G : ∀ g, Cart V d (I g) (J g)) (alt : Prop) {N : ℕ}
    (P : MvPolynomial (Fin N × WV I) C) (kind : Fin N → Option (Fin 2 × ZMod d × ZMod d))
    (h : RowsOK G alt P kind) (ρ : Fin N) (μ μ' : Fin N × WV I →₀ ℕ) (hμ : μ ∈ P.support)
    (hμ' : μ' ∈ P.support) (w w' : WV I) (hw : μ (ρ, w) ≠ 0) (hw' : μ' (ρ, w') ≠ 0)
    (hne : w.1 ≠ w'.1) : alt ∧ tyW G w ≠ tyW G w' := by sorry
