-- Prove2me | Theorems.Thm_IncoherentPurity_Adaptive_povm_simulation
-- name    : IncoherentPurity.Adaptive.povm_simulation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:07.180686+00:00
-- url     : https://prove2.me/theorems/feb3a552-409e-4808-b744-3877a3ad7259
-- title:
--   Lemma 6.6 — Bounded-query simulation
-- statement:
--   There is one absolute $C>0$ such that for every $d\ge1$, encoding basis, and adaptive schedule of $n$ single-copy POVMs, a parameter-independent simulator uses at most $\lceil Cn\rceil$ adaptive noisy linear queries of norm at most $d$. On every vector input, including invalid encodings, it terminates at this fixed cap and returns an output. If the encoding is a state and $\|\Delta_\theta\|_\infty\le1/(2d)$, its output and the ideal seeded transcript admit a coupling with
--
--   $$\Pr(\text{simulated transcript}=\text{ideal transcript})\ge .99.$$
--
--   The guarantee includes equality at the norm boundary. Output on failure is unrestricted; no claim is made that conditioning on no timeout preserves the exact Born law.
--
--   Differences from the source:
--   - encoding: matrix, probability and asymptotic notation in the paper → finite matrix coordinates, explicit experiment measures, and universal real constants; reason: the representations retain every source instance and clause; finite-moment conclusions prevent default-zero integrals
--   - encoding: Cn noisy queries and exact simulation with probability at least .99, with arbitrary output on failure → a fixed padded ceiling budget on every input and a measurable .99 agreement coupling on good inputs; reason: integer budgets and the stated probabilistic exact simulation are preserved, including equality at the good-input boundary
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce, Lemma 6.6, PDF p.20 = printed p.20

import Definitions.Def_IncoherentPurity_Adaptive_Estimators
import Definitions.Def_IncoherentPurity_Adaptive_Analytic

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Frobenius
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive

/-- Lemma 6.6, PDF p.20, pinned source hash 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce. -/
theorem povm_simulation : ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 0 < d → ∀ (E : Encoding d) (n : ℕ) (P : Protocol d),
  ∃ S : QueryPolicy (gaussDim d) (P.Seed × (ℕ → (Unit ⊕ P.Outcome))),
    IsBoundedQuery S (d : ℝ) ∧
    (∀ θ, IsProbabilityMeasure (queryOutputLawAt S ⌈C*(n : ℝ)⌉₊ θ)) ∧
    ∀ θ (hρ : ProjectiveMeasurementEquilibration.IsDensityMatrix (encoded E θ)),
      opNorm (perturbation E θ) ≤ 1/(2*(d : ℝ)) →
      Nonempty (Coupling _ (queryOutputLawAt S ⌈C*(n : ℝ)⌉₊ θ)
        (transcriptLaw P ⟨encoded E θ,hρ⟩ n) (99/100)) := by sorry

end IncoherentPurity.Adaptive
