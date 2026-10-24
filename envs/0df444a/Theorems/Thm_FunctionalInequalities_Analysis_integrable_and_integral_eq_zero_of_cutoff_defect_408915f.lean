-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integrable_and_integral_eq_zero_of_cutoff_defect_408915f
-- name    : FunctionalInequalities.Analysis.integrable_and_integral_eq_zero_of_cutoff_defect_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:26:04.270987+00:00
-- url     : https://prove2.me/theorems/8fd5208c-eeba-4056-a349-a30cc7adaecc
-- title:
--   Conservativity From Cutoff Defects
-- statement:
--   This formalizes Lemma A.5 of Letwin (arXiv:2607.24164v1), cited as the mean-zero statement for $Lf$.
--
--   Let μ be a probability measure on a measurable space α, and let f,g:α→ℝ be almost-everywhere strongly measurable. Assume
--
--   1. there is C≥0 such that $|f|\leq C$ μ-a.e.;
--   2. there is c>0 such that $g+cf\geq0$ μ-a.e.;
--   3. χₙ and dₙ are sequences of functions, each χₙ is almost-everywhere strongly measurable and satisfies $0\leqχₙ\leq1$ μ-a.e.;
--   4. χₙ(x)→1 for μ-a.e. x;
--   5. every dₙ is integrable and $\int|d_n|\,d\mu\to0$;
--   6. every χₙg is integrable; and
--   7. for every n,
--      $$\int χ_n g\,d\mu=\int f d_n\,d\mu.$$
--
--   Then g is integrable and has zero integral:
--
--   $$g\in L^1(\mu)\qquad\text{and}\qquad\int g\,d\mu=0.$$
--
--   This is a general cutoff-conservativity principle: neither integrability of g nor its zero integral is assumed initially.
--
--   **Formalization Note** The measure is a `ProbabilityMeasure`; all convergence and inequalities involving χₙ are stated μ-a.e., and the integrals are ordinary real integrals.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Cutoff/Conservativity.lean#L23-L208 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Cutoff.Conservativity`, declaration `FunctionalInequalities.Analysis.integrable_and_integral_eq_zero_of_cutoff_defect`; the repository is private at upload time).

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

noncomputable section
open MeasureTheory Filter
open scoped Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.integrable_and_integral_eq_zero_of_cutoff_defect_408915f
    {α : Type*} [MeasurableSpace α] (mu : ProbabilityMeasure α)
    (f g : α → ℝ) (hf : AEStronglyMeasurable f (mu : Measure α))
    (hg : AEStronglyMeasurable g (mu : Measure α))
    (C : ℝ) (hC : 0 ≤ C) (hfBound : ∀ᵐ x ∂(mu : Measure α), |f x| ≤ C)
    (c : ℝ) (hc : 0 < c)
    (hLower : ∀ᵐ x ∂(mu : Measure α), 0 ≤ g x + c * f x)
    (chi defect : ℕ → α → ℝ)
    (hChiMeas : ∀ n, AEStronglyMeasurable (chi n) (mu : Measure α))
    (hChiBounds : ∀ n, ∀ᵐ x ∂(mu : Measure α), 0 ≤ chi n x ∧ chi n x ≤ 1)
    (hChiLim : ∀ᵐ x ∂(mu : Measure α), Tendsto (fun n => chi n x) atTop (𝓝 1))
    (hDefect : ∀ n, Integrable (defect n) (mu : Measure α))
    (hDefectLim : Tendsto (fun n => ∫ x, |defect n x| ∂(mu : Measure α)) atTop (𝓝 0))
    (hCutoffG : ∀ n, Integrable (fun x => chi n x * g x) (mu : Measure α))
    (hSym : ∀ n, (∫ x, chi n x * g x ∂(mu : Measure α)) =
      ∫ x, f x * defect n x ∂(mu : Measure α)) :
    Integrable g (mu : Measure α) ∧ (∫ x, g x ∂(mu : Measure α)) = 0 := by sorry
