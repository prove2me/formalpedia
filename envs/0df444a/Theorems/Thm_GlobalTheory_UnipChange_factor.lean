-- Prove2me | Theorems.Thm_GlobalTheory_UnipChange_factor
-- name    : GlobalTheory.UnipChange.factor
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:43:06.935531+00:00
-- url     : https://prove2.me/theorems/449eb386-718a-47fb-9746-325bbb4a3c40
-- title:
--   Unip Change: factor
-- statement:
--   The Unip Change construction uses the factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitriangularMapInduction.lean#L297-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitriangularMapInduction.lean#L297-L338

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointRadical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitriangularMapInduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped Pointwise
open GlobalTheory GlobalTheory.UnipChange
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointRadical
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k]
  {r : ℕ} {b : Fin r → ℕ}

theorem GlobalTheory.UnipChange.factor (L : lieRadical k b ≃ₗ[k] lieRadical k b)
    (hL : ∀ t (X : lieRadical k b), X.1 ∈ filt k b t → (L X).1 ∈ filt k b t)
    (f : radical k b → radical k b) (hf : Continuous f)
    (hd : ∀ t n n', (lg n - lg n').1 ∈ filt k b t →
      ((lg (f n) - L (lg n)) - (lg (f n') - L (lg n'))).1 ∈ filt k b (t + 1)) :
    ∃ (L' : (Pos b → k) ≃ₗ[k] Pos b → k) (g : (Pos b → k) → Pos b → k),
      LinearMap.det (L' : (Pos b → k) →ₗ[k] Pos b → k)
        = LinearMap.det (L : lieRadical k b →ₗ[k] lieRadical k b) ∧ Continuous g ∧
      (∀ x y i, (∀ j : Pos b, b j.1.2 - b j.1.1 < b i.1.2 - b i.1.1 → x j = y j) → g x i = g y i) ∧
      f ∘ chart k b = chart k b ∘ L' ∘ fun x => x + g x := by sorry
