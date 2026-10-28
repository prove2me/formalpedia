-- Prove2me | Theorems.Thm_OAI_Kadison_SchurWeyl_centered_expansion_contractions
-- name    : OAI.Kadison.SchurWeyl.centered_expansion_contractions
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:49:06.84299+00:00
-- url     : https://prove2.me/theorems/c185445f-3c2d-49d1-bf85-1f4a4afcd27b
-- title:
--   OAI.Kadison.SchurWeyl.centered_expansion_contractions: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.SchurWeyl`, with `open scoped ComplexOrder InnerProductSpace`, `open Complex ContinuousLinearMap UniformSpace Completion`, `open scoped InnerProductSpace`, `open scoped TensorProduct`, `open scoped TensorProduct InnerProductSpace Topology`, `open UniformSpace Completion Filter`, `open scoped TensorProduct`, `open UniformSpace Completion`, `open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder`):
--
--   ```lean
--   theorem centered_expansion_contractions (d : Equiv.Perm (Option J) → ℂ)
--       (hd : ∀ σ, 2 * cycleCount σ < Fintype.card (Option J) + 1 → d σ = 0)
--       (A : Option J → Matrix I I ℂ) (hA : ∀ j, Matrix.trace (A (some j)) = 0) :
--       (∑ σ, d σ * cycleTrace σ A) =
--         ((Fintype.card I : ℂ)⁻¹ * Matrix.trace (A none)) *
--           ∑ τ : Pairing J, d (endpointPairingPerm τ) *
--             Pairing.contraction τ
--               (fun X Y => (Fintype.card I : ℂ)⁻¹ * Matrix.trace (X * Y))
--               (fun j => A (some j))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.Pairing`, `OAI.Kadison.Pairing.contraction` and `OAI.Kadison.Pairing.instFintype` (definitions bundle `OAIQ039C015` of this split); `OAI.Kadison.SchurWeyl.cycleCount`, `OAI.Kadison.SchurWeyl.cycleTrace` and `OAI.Kadison.SchurWeyl.endpointPairingPerm` (definitions bundle `OAIQ039C029` of this split).
--
--   **Used by.** The proofs of `OAI.Kadison.TracialGNS.stageCoefficient_crossing` and `OAI.Kadison.TracialGNS.stage_pairing_expansion` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C029

section

attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
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

namespace Kadison.SchurWeyl

variable {J : Type*}

variable [Fintype J] [LinearOrder J]

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem centered_expansion_contractions (d : Equiv.Perm (Option J) → ℂ)
    (hd : ∀ σ, 2 * cycleCount σ < Fintype.card (Option J) + 1 → d σ = 0)
    (A : Option J → Matrix I I ℂ) (hA : ∀ j, Matrix.trace (A (some j)) = 0) :
    (∑ σ, d σ * cycleTrace σ A) =
      ((Fintype.card I : ℂ)⁻¹ * Matrix.trace (A none)) *
        ∑ τ : Pairing J, d (endpointPairingPerm τ) *
          Pairing.contraction τ
            (fun X Y => (Fintype.card I : ℂ)⁻¹ * Matrix.trace (X * Y))
            (fun j => A (some j)) := by
  sorry

end Kadison.SchurWeyl
end

end OAI
end
