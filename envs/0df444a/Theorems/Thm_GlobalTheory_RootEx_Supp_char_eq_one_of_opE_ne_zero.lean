-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Supp_char_eq_one_of_opE_ne_zero
-- name    : GlobalTheory.RootEx.Supp.char_eq_one_of_opE_ne_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:28:29.695238+00:00
-- url     : https://prove2.me/theorems/958f5d07-0262-4519-8ba3-c2e7a792d166
-- title:
--   Supp: char eq one of op E ne zero
-- statement:
--   The Supp construction uses the char eq one of op E ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CharEqOneOfOpENeZero.lean#L212-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CharEqOneOfOpENeZero.lean#L212-L240

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Supp

theorem GlobalTheory.RootEx.Supp.char_eq_one_of_opE_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n'] {c p : ℕ} (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
    (F : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) (hF : opE ψ ν p F x₀ ≠ 0)
    (d : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (hd : ∀ r s, ¬ Free p (r, s) → d r s = 0)
    (hFd : ∀ x, F (x + d) = F x) : ψ (ch d) = 1 := by sorry
