-- Prove2me | Theorems.Thm_OAI_Percolation_critical_rootTriangleSqrt_derivative_bs
-- name    : OAI.Percolation.critical_rootTriangleSqrt_derivative_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:41:52.762781+00:00
-- url     : https://prove2.me/theorems/1143b328-3f84-4550-bc40-7bb06e448656
-- title:
--   OAI.Percolation.critical_rootTriangleSqrt_derivative_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.critical_rootTriangleSqrt_derivative` of [lean/OAI/Probability/UnimodularPercolation/Kernel/TraceBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/Kernel/TraceBounds.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`, `open MeasureTheory`):
--
--   ```lean
--   theorem critical_rootTriangleSqrt_derivative_bs
--       [Countable V] [Countable E] [Nonempty V] [Nonempty E]
--       (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
--       (hqt : QuasiTransitive G) (hh : 0 < hV G)
--       {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
--       (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
--       (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
--       (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
--       (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
--       (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
--       (α ε : ℝ) (hα : 0 < α) (hα1 : α < 1/2) (hε : 0 < ε)
--       (hr : (1:ℝ)/2+ε-2*α < 0) :
--       ∃ C : ℝ, 0 < C ∧ ∀ (p : unitInterval),
--         (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
--         ∀ (T : Hilbert V →L[ℂ] Hilbert V), HasKernel G p T →
--         ∀ L : ℝ, 1 ≤ L →
--           deriv (rootTriangleSqrt G root weight) (p:ℝ) ≤
--           C*L^(1-α)*rootTriangleSqrt G root weight (p:ℝ) +
--             C*L^(((1:ℝ)/2+ε-2*α)/2)*‖T‖^((3:ℝ)/2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.RootTransport` (definitions bundle `OAIQ078B001` of this split); `OAI.Percolation.rootTriangleSqrt` and `OAI.Percolation.vertexAut` (definitions bundle `OAIQ078B002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.Connected`, `OAI.Percolation.HasKernel`, `OAI.Percolation.Hilbert`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.QuasiTransitive`, `OAI.Percolation.cluster`, `OAI.Percolation.hV`, `OAI.Percolation.law` and `OAI.Percolation.pc` (the published bundle `Def_BenjaminiSchramm`).
--
--   **Used by.** The proof of `OAI.Percolation.critical_bounded_of_transport_finiteness_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/Kernel/TraceBounds.lean (declaration OAI.Percolation.critical_rootTriangleSqrt_derivative)

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002

section

attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section TraceSquareRoot
attribute [local instance] Classical.propDecidable Classical.decEq

theorem critical_rootTriangleSqrt_derivative_bs
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
    (α ε : ℝ) (hα : 0 < α) (hα1 : α < 1/2) (hε : 0 < ε)
    (hr : (1:ℝ)/2+ε-2*α < 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : unitInterval),
      (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      ∀ (T : Hilbert V →L[ℂ] Hilbert V), HasKernel G p T →
      ∀ L : ℝ, 1 ≤ L →
        deriv (rootTriangleSqrt G root weight) (p:ℝ) ≤
        C*L^(1-α)*rootTriangleSqrt G root weight (p:ℝ) +
          C*L^(((1:ℝ)/2+ε-2*α)/2)*‖T‖^((3:ℝ)/2) := by
  sorry

end TraceSquareRoot
end Percolation

end OAI
end
