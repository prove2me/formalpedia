-- Prove2me | Theorems.Thm_OAI_Kadison_finite_pairing_source_bound
-- name    : OAI.Kadison.finite_pairing_source_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:39:15.764178+00:00
-- url     : https://prove2.me/theorems/ddee7772-feec-4791-9ec2-29bb8a2ad280
-- title:
--   OAI.Kadison.finite_pairing_source_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison`, with `open scoped ComplexOrder InnerProductSpace`, `open Complex ContinuousLinearMap UniformSpace Completion`, `open scoped InnerProductSpace`, `open scoped TensorProduct`, `open scoped TensorProduct InnerProductSpace Topology`, `open UniformSpace Completion Filter`, `open scoped TensorProduct`, `open UniformSpace Completion`, `open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder`, `open PreHilbert`):
--
--   ```lean
--   lemma finite_pairing_source_bound (E F : PreHilbert) (k l N : ℕ)
--       (Ω : E) (hΩ : ‖Ω‖ = 1) (T : wordSpace E F k →L[ℂ] wordSpace E F l)
--       (c : Pairing (TailSlots k l) → ℂ) (h : TailSlots k l × Fin (N+1) → F)
--       (horth : Orthonormal ℂ h)
--       (hexp : ∀ v : TailSlots k l → TailSlots k l × Fin (N+1),
--         inner ℂ (word E F l Ω (fun j => h (v (.inr j))))
--           (T (word E F k Ω (fun i => h (v (.inl i))))) =
--           ∑ σ, c σ * Pairing.contraction σ (fun a b => if a = b then 1 else 0) v)
--       (τ : Pairing (TailSlots k l)) (a b : Fin k) (hab : τ (.inl a) = .inl b) :
--       (N+1 : ℝ) * ‖c τ‖ ^ 2 ≤ ‖T‖ ^ 2
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.PreHilbert`, `OAI.Kadison.PreHilbert.power`, `OAI.Kadison.PreHilbert.word` and `OAI.Kadison.PreHilbert.wordSpace` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.TailSlots` (definitions bundle `OAIQ039C014` of this split); `OAI.Kadison.Pairing`, `OAI.Kadison.Pairing.contraction` and `OAI.Kadison.Pairing.instFintype` (definitions bundle `OAIQ039C015` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialGNS.stage_pairing_same_side_zero` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C010
import Definitions.Def_OAIQ039C014
import Definitions.Def_OAIQ039C015

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison

open PreHilbert

lemma finite_pairing_source_bound (E F : PreHilbert) (k l N : ℕ)
    (Ω : E) (hΩ : ‖Ω‖ = 1) (T : wordSpace E F k →L[ℂ] wordSpace E F l)
    (c : Pairing (TailSlots k l) → ℂ) (h : TailSlots k l × Fin (N+1) → F)
    (horth : Orthonormal ℂ h)
    (hexp : ∀ v : TailSlots k l → TailSlots k l × Fin (N+1),
      inner ℂ (word E F l Ω (fun j => h (v (.inr j))))
        (T (word E F k Ω (fun i => h (v (.inl i))))) =
        ∑ σ, c σ * Pairing.contraction σ (fun a b => if a = b then 1 else 0) v)
    (τ : Pairing (TailSlots k l)) (a b : Fin k) (hab : τ (.inl a) = .inl b) :
    (N+1 : ℝ) * ‖c τ‖ ^ 2 ≤ ‖T‖ ^ 2 := by
  sorry

end Kadison
end

end OAI
end
