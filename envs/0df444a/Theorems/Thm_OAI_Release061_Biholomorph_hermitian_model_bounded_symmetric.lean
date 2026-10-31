-- Prove2me | Theorems.Thm_OAI_Release061_Biholomorph_hermitian_model_bounded_symmetric
-- name    : OAI.Release061.Biholomorph.hermitian_model_bounded_symmetric
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T21:48:54.452262+00:00
-- url     : https://prove2.me/theorems/d7830a61-4382-44ad-be33-9215f2d77ae9
-- title:
--   OAI.Release061.Biholomorph.hermitian_model_bounded_symmetric: intermediate lemma from OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Release061.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symmetry of semialgebraic bounded domains with compact quotient (result family 058)*, OpenAI Math Release, September 24, 2026, result family 58, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Release061.Biholomorph.hermitian_model_bounded_symmetric` of [lean/OAI/Analysis/SymmetricDomains/HermitianModelSymmetric.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/HermitianModelSymmetric.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Release061.Biholomorph`, with `open Set Metric Complex`, `open scoped Topology`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped Topology ContDiff`, `open Filter`, `open scoped BigOperators Topology ContDiff`, `open Set Filter MeasureTheory`, `open scoped Topology`, `open Set Filter`, `open Set Metric`, `open scoped Topology`, `open Set Filter Metric`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter Metric`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open Set Filter Topology`, `open Filter Topology`, `open Filter Topology`, `open Filter Topology`, `open Filter Topology`, `open Polynomial`, `open Filter Topology`, `open scoped TensorProduct`, `open Set Filter Topology`, `open scoped TensorProduct`, `open scoped TensorProduct`, `open Filter Topology`, `open Filter Topology`, `open scoped TensorProduct`, `open Filter Topology`, `open scoped TensorProduct`, `open scoped TensorProduct`, `open scoped TensorProduct`, `open Filter Topology`, `open scoped TensorProduct`, `open Set Filter Topology`):
--
--   ```lean
--   theorem hermitian_model_bounded_symmetric {r k : ℕ}
--       (B : Fin k → Affine r →ₗ[ℝ] Affine r →ₗ[ℝ] ℝ) (C : Set (Fin k → ℝ))
--       (hDo : IsOpen (quadraticDomain (Hermitian.hermQuadratic B) C))
--       (htr : ∀ p : Affine r × Affine k, ∀ a : Fin k → ℝ,
--         (p.1,fun i => p.2 i+(a i : ℂ)) ∈ quadraticDomain (Hermitian.hermQuadratic B) C ↔
--           p∈quadraticDomain (Hermitian.hermQuadratic B) C)
--       (hd : ∀ t : ℝ, 0<t → ∀ p, (Real.sqrt t • p.1,t • p.2)∈
--         quadraticDomain (Hermitian.hermQuadratic B) C ↔ p∈quadraticDomain (Hermitian.hermQuadratic B) C)
--       (hr : ∀ c : ℂ, ‖c‖=1 → ∀ p, (c • p.1,p.2)∈quadraticDomain (Hermitian.hermQuadratic B) C ↔
--         p∈quadraticDomain (Hermitian.hermQuadratic B) C)
--       [LocallyCompactSpace ((affineProductCoordinates r k) '' quadraticDomain (Hermitian.hermQuadratic B) C)]
--       (e : Biholomorph ((affineProductCoordinates r k) '' quadraticDomain (Hermitian.hermQuadratic B) C) U) :
--       IsBoundedSymmetricDomain U
--   ```
--
--   **Definitions.** The statement is written with `OAI.Release061.affineProductCoordinates` (definitions bundle `OAIQ025S000` of this split); `OAI.Release061.Hermitian.hermQuadratic` (definitions bundle `OAIQ025S001` of this split); `OAI.Release061.quadraticDomain` (definitions bundle `OAIQ025S002` of this split); `OAI.Release061.Affine`, `OAI.Release061.Biholomorph`, `OAI.Release061.HolomorphicOnSubset` and `OAI.Release061.IsBoundedSymmetricDomain` (the published bundle `Def_SymmetricDomains`).
--
--   **Used by.** The proof of `OAI.Release061.main` of this split imports it.
-- source:
--   OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 58; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symmetry-of-semialgebraic-bounded-domains-with-compact-quotient-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/HermitianModelSymmetric.lean (declaration OAI.Release061.Biholomorph.hermitian_model_bounded_symmetric)

import Mathlib
import Definitions.Def_SymmetricDomains
import Definitions.Def_OAIQ025S000
import Definitions.Def_OAIQ025S001
import Definitions.Def_OAIQ025S002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set Filter Topology
namespace Biholomorph

variable {n : ℕ} {U : Set (Affine n)}
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U] [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))

include hU hc hbd Γ hhol in

theorem hermitian_model_bounded_symmetric {r k : ℕ}
    (B : Fin k → Affine r →ₗ[ℝ] Affine r →ₗ[ℝ] ℝ) (C : Set (Fin k → ℝ))
    (hDo : IsOpen (quadraticDomain (Hermitian.hermQuadratic B) C))
    (htr : ∀ p : Affine r × Affine k, ∀ a : Fin k → ℝ,
      (p.1,fun i => p.2 i+(a i : ℂ)) ∈ quadraticDomain (Hermitian.hermQuadratic B) C ↔
        p∈quadraticDomain (Hermitian.hermQuadratic B) C)
    (hd : ∀ t : ℝ, 0<t → ∀ p, (Real.sqrt t • p.1,t • p.2)∈
      quadraticDomain (Hermitian.hermQuadratic B) C ↔ p∈quadraticDomain (Hermitian.hermQuadratic B) C)
    (hr : ∀ c : ℂ, ‖c‖=1 → ∀ p, (c • p.1,p.2)∈quadraticDomain (Hermitian.hermQuadratic B) C ↔
      p∈quadraticDomain (Hermitian.hermQuadratic B) C)
    [LocallyCompactSpace ((affineProductCoordinates r k) '' quadraticDomain (Hermitian.hermQuadratic B) C)]
    (e : Biholomorph ((affineProductCoordinates r k) '' quadraticDomain (Hermitian.hermQuadratic B) C) U) :
    IsBoundedSymmetricDomain U := by
  sorry

end Biholomorph
end Release061

end

end OAI
end
