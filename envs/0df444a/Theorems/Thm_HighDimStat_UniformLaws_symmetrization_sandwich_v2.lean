-- Prove2me | Theorems.Thm_HighDimStat_UniformLaws_symmetrization_sandwich_v2
-- name    : HighDimStat.UniformLaws.symmetrization_sandwich_v2
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:20:43.368868+00:00
-- url     : https://prove2.me/theorems/6fe9c8e5-351e-4b7b-af85-af586ac88419
-- title:
--   Proposition 4.11 — the symmetrization sandwich (i.i.d. sample, independent Rademacher signs)
-- statement:
--   **Proposition 4.11 (symmetrization sandwich).** Let $\mathcal F=\{f_j\}_{j\in\iota}$ be a
--   countable class of measurable, $\mathbb P$-integrable real functions on $\mathcal D$ that is
--   pointwise bounded ($\sup_j|f_j(x)|<\infty$ for every $x$) with bounded means
--   ($\sup_j|\mathbb E f_j(X)|<\infty$). Let $X_1,\dots,X_n$ be i.i.d. with the law $\mathbb P$ of
--   $X_0$, and let $\varepsilon_1,\dots,\varepsilon_n$ be i.i.d. Rademacher signs
--   ($\mathbb P[\varepsilon_i=1]=\mathbb P[\varepsilon_i=-1]=\tfrac12$) independent of the sample.
--   Then for any convex non-decreasing function $\Phi:\mathbb R\to\mathbb R$,
--
--   $$
--   \mathbb E_{X,\varepsilon}\big[\Phi(\tfrac12\|S_n\|_{\bar{\mathcal F}})\big] \;\le\;
--   \mathbb E_X\big[\Phi(\|\mathbb P_n-\mathbb P\|_{\mathcal F})\big] \;\le\;
--   \mathbb E_{X,\varepsilon}\big[\Phi(2\|S_n\|_{\mathcal F})\big],
--   $$
--
--   where $\|\mathbb P_n-\mathbb P\|_{\mathcal F}=\sup_{f\in\mathcal F}|\frac1n\sum_i f(X_i)-\mathbb E f(X)|$,
--   $\|S_n\|_{\mathcal F}=\sup_{f\in\mathcal F}|\frac1n\sum_i\varepsilon_i f(X_i)|$ (Eqs. (4.7), (4.19)),
--   and $\bar{\mathcal F}=\{f-\mathbb E[f],\ f\in\mathcal F\}$ is the recentered class.
--
--   This "sandwich" result is what makes the symmetrization technique used in Theorem 4.10's
--   proof more than a one-off trick: the empirical process and its symmetrized version are
--   equivalent up to universal constants for *any* convex non-decreasing test function.
--
--   **Formalization Note.** The retired version (`symmetrization_sandwich`) quantified over
--   arbitrary maps $X_i$, $X_0$, $\varepsilon_i$ with no distributional assumption at all, so taking
--   $\varepsilon\equiv 0$ refuted it (accepted disproof). The new statement adds the probabilistic
--   model of the section: the $X_i$ ($i<n$) are measurable and identically distributed with $X_0$
--   (`hXid`), mutually independent (`hXindep`); the $\varepsilon_i$ are measurable Rademacher
--   (`heps_law`), mutually independent (`hepsindep`), and the sign vector is independent of the
--   sample vector (`hXeps`) — together this is the mutual independence of
--   $(X_1,\dots,X_n,\varepsilon_1,\dots,\varepsilon_n)$ with the stated marginals. Conventions made
--   explicit: `[Countable ι]` (the field's standing measurability convention under which suprema
--   of empirical processes are measurable; the book assumes measurability throughout), each $f_j$
--   measurable and $\mathbb P$-integrable (Chapter 4's "class of integrable functions"; without
--   integrability the Bochner mean $\mathbb E f_j(X)$ would be Mathlib's junk value $0$), and the
--   finiteness of the three suprema (`hbdd`, `hbddE`), without which Mathlib's real `⨆` returns the
--   junk value $0$ for an unbounded family and the inequality is false even under the i.i.d.
--   model. The `Integrable` hypotheses on the three $\Phi$-composed quantities are kept from the
--   retired version. The lower bound uses the symmetrized process of the recentered class and the
--   upper bound the un-recentered one, exactly as in the displayed inequality (4.20).
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 107 (PDF p. 127), Proposition 4.11, Eq. (4.20)

import Mathlib
import Definitions.Def_HighDimStat_UniformLaws_empProcessDeviation
import Definitions.Def_HighDimStat_UniformLaws_symmetrizedProcess

open MeasureTheory ProbabilityTheory

namespace HighDimStat.UniformLaws

/-- **Proposition 4.11** (symmetrization sandwich), Wainwright, *High-Dimensional Statistics*
(2019), Eq. (4.20), p. 107. Let `F = {f_j, j ∈ ι}` be a class of measurable, `P`-integrable
functions, let `X₁,…,Xₙ` be i.i.d. with the law `P` of `X₀`, and let `ε₁,…,εₙ` be i.i.d.
Rademacher signs independent of the sample (the probabilistic model of Eqs. (4.7)/(4.19)).
Then for any convex non-decreasing `Φ : ℝ → ℝ`,
`E[Φ((1/2)‖Sₙ‖_F̄)] ≤ E[Φ(‖Pₙ-P‖_F)] ≤ E[Φ(2‖Sₙ‖_F)]`, where `F̄ = {f-E[f], f∈F}` is the
recentered function class.

Corrections relative to the retired version, which quantified over arbitrary `Xs`, `X0`, `eps`:
the sample is now i.i.d. with the law of `X0` (`hXid`, `hXindep`), the signs are Rademacher
(`heps_law`, `hepsindep`) and independent of the sample (`hXeps`). Conventions made explicit:
`F` countable (the field's standing measurability convention for suprema of empirical
processes), each `f_j` measurable and `P`-integrable, and the suprema finite (`F` pointwise
bounded with bounded means), which is what makes the three real-valued suprema the book's
quantities rather than Mathlib's junk value `0` for an unbounded `⨆`. The `Integrable`
hypotheses on the three `Φ`-composed quantities guard the Bochner integrals. -/
theorem symmetrization_sandwich_v2 {D ι Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω]
    [Countable ι]
    {Prob : Measure Ω} [IsProbabilityMeasure Prob] (f : ι → D → ℝ) (hf : ∀ j, Measurable (f j))
    (Xs : ℕ → Ω → D) (X0 : Ω → D) (eps : ℕ → Ω → ℝ) (n : ℕ)
    (hXmeas : ∀ i, Measurable (Xs i))
    (hXid : ∀ i, i < n → IdentDistrib (Xs i) X0 Prob Prob)
    (hXindep : iIndepFun (fun i : Fin n => Xs i) Prob)
    (heps_meas : ∀ i, Measurable (eps i))
    (heps_law : ∀ i, i < n →
      Prob {ω | eps i ω = 1} = 1 / 2 ∧ Prob {ω | eps i ω = -1} = 1 / 2)
    (hepsindep : iIndepFun (fun i : Fin n => eps i) Prob)
    (hXeps : IndepFun (fun ω (i : Fin n) => Xs i ω) (fun ω (i : Fin n) => eps i ω) Prob)
    (hfint : ∀ j, Integrable (fun ω => f j (X0 ω)) Prob)
    (hbdd : ∀ x, BddAbove (Set.range fun j => |f j x|))
    (hbddE : BddAbove (Set.range fun j => |∫ ω', f j (X0 ω') ∂Prob|))
    (Φ : ℝ → ℝ) (hΦconv : ConvexOn ℝ Set.univ Φ) (hΦmono : Monotone Φ)
    (hInt1 : Integrable (fun ω => Φ (1 / 2 *
      symmetrizedProcess (fun j x => f j x - ∫ ω', f j (X0 ω') ∂Prob) Xs eps n ω)) Prob)
    (hInt2 : Integrable (fun ω => Φ (empProcessDeviation f Xs X0 Prob n ω)) Prob)
    (hInt3 : Integrable (fun ω => Φ (2 * symmetrizedProcess f Xs eps n ω)) Prob) :
    ∫ ω, Φ (1 / 2 *
      symmetrizedProcess (fun j x => f j x - ∫ ω', f j (X0 ω') ∂Prob) Xs eps n ω) ∂Prob ≤
    ∫ ω, Φ (empProcessDeviation f Xs X0 Prob n ω) ∂Prob
    ∧
    ∫ ω, Φ (empProcessDeviation f Xs X0 Prob n ω) ∂Prob ≤
    ∫ ω, Φ (2 * symmetrizedProcess f Xs eps n ω) ∂Prob := by sorry

end HighDimStat.UniformLaws
