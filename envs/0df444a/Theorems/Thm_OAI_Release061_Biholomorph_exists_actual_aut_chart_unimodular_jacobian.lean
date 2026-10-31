-- Prove2me | Theorems.Thm_OAI_Release061_Biholomorph_exists_actual_aut_chart_unimodular_jacobian
-- name    : OAI.Release061.Biholomorph.exists_actual_aut_chart_unimodular_jacobian
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T21:49:36.366194+00:00
-- url     : https://prove2.me/theorems/e9f24269-e550-4acd-90c2-e16fe8c0ddff
-- title:
--   OAI.Release061.Biholomorph.exists_actual_aut_chart_unimodular_jacobian: intermediate lemma from OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Release061.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symmetry of semialgebraic bounded domains with compact quotient (result family 058)*, OpenAI Math Release, September 24, 2026, result family 58, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Release061.Biholomorph.exists_actual_aut_chart_unimodular_jacobian` of [lean/OAI/Analysis/SymmetricDomains/AutChartUnimodularJacobian.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/AutChartUnimodularJacobian.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Release061.Biholomorph`, with `open Set Metric Complex`, `open scoped Topology`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped Topology ContDiff`, `open Filter`, `open scoped BigOperators Topology ContDiff`, `open Set Filter MeasureTheory`, `open scoped Topology`, `open Set Filter`, `open Set Metric`, `open scoped Topology`, `open Set Filter Metric`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter Metric`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open Set Filter Topology`, `open Filter Topology`, `open Filter Topology`, `open Filter Topology`, `open Filter Topology`, `open Polynomial`, `open Filter Topology`, `open scoped TensorProduct`, `open Set Filter Topology`, `open scoped TensorProduct`, `open scoped TensorProduct`, `open Filter Topology`, `open Filter Topology`, `open scoped TensorProduct`, `open Filter Topology`, `open scoped TensorProduct`, `open scoped TensorProduct`, `open scoped TensorProduct`, `open Filter Topology`, `open scoped TensorProduct`, `open Set Filter Topology MeasureTheory`):
--
--   ```lean
--   theorem exists_actual_aut_chart_unimodular_jacobian :
--       ∃ P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ]
--           LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p),
--       ∃ e : OpenPartialHomeomorph (Biholomorph U U)
--           (LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)),
--         (e : Biholomorph U U → _)=(fun a => P (ambientFirstJet p a)) ∧
--         1∈e.source ∧
--         (∀ X : completeGeneratorSpace hU hc hbd Γ hhol,
--           (P (completeGeneratorFirstJet hU hc hbd Γ hhol p X)).val=
--             completeGeneratorFirstJet hU hc hbd Γ hhol p X) ∧
--         (∀ (p' : U) y, y∈e.target →
--           ContDiffAt ℝ 1 (fun t => ambientFirstJet p' (e.symm t)) y) ∧
--         ∀ g : Biholomorph U U,
--           |(fderiv ℝ (fun x => e (g*e.symm x*g⁻¹)) (e 1)).det|=1
--   ```
--
--   **Definitions.** The statement is written with `OAI.Release061.Biholomorph.ambientFirstJet`, `OAI.Release061.Biholomorph.automorphismInv`, `OAI.Release061.Biholomorph.automorphismMul`, `OAI.Release061.Biholomorph.automorphismOne`, `OAI.Release061.Biholomorph.automorphismTopology`, `OAI.Release061.Biholomorph.completeGeneratorFirstJet` and `OAI.Release061.Biholomorph.completeGeneratorSpace` (definitions bundle `OAIQ025S000` of this split); `OAI.Release061.Affine`, `OAI.Release061.Biholomorph` and `OAI.Release061.HolomorphicOnSubset` (the published bundle `Def_SymmetricDomains`).
--
--   **Used by.** The proof of `OAI.Release061.Biholomorph.hermitian_model_bounded_symmetric` of this split imports it.
-- source:
--   OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 58; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symmetry-of-semialgebraic-bounded-domains-with-compact-quotient-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/AutChartUnimodularJacobian.lean (declaration OAI.Release061.Biholomorph.exists_actual_aut_chart_unimodular_jacobian)

import Mathlib
import Definitions.Def_SymmetricDomains
import Definitions.Def_OAIQ025S000

section

attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
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
open Set Filter Topology MeasureTheory

namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U)
include hU hc hbd Γ hhol

theorem exists_actual_aut_chart_unimodular_jacobian :
    ∃ P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ]
        LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p),
    ∃ e : OpenPartialHomeomorph (Biholomorph U U)
        (LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)),
      (e : Biholomorph U U → _)=(fun a => P (ambientFirstJet p a)) ∧
      1∈e.source ∧
      (∀ X : completeGeneratorSpace hU hc hbd Γ hhol,
        (P (completeGeneratorFirstJet hU hc hbd Γ hhol p X)).val=
          completeGeneratorFirstJet hU hc hbd Γ hhol p X) ∧
      (∀ (p' : U) y, y∈e.target →
        ContDiffAt ℝ 1 (fun t => ambientFirstJet p' (e.symm t)) y) ∧
      ∀ g : Biholomorph U U,
        |(fderiv ℝ (fun x => e (g*e.symm x*g⁻¹)) (e 1)).det|=1 := by
  sorry
end Biholomorph
end Release061

end

end OAI
end
