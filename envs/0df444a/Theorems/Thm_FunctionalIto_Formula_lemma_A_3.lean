-- Prove2me | Theorems.Thm_FunctionalIto_Formula_lemma_A_3
-- name    : FunctionalIto.Formula.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:25.305983+00:00
-- url     : https://prove2.me/theorems/f5a448cd-e37b-4cdf-b328-a3e5fbca63a0
-- title:
--   Lemma A.3, p. 22 — uniform approximation of cadlag functions by step functions (65)
-- statement:
--   Let $f\in D([0,T],\mathbb R^d)$ be cadlag and let $\pi^n=(t^n_i)_{i=0,\dots,k_n}$ be partitions $0=t^n_0<t^n_1<\dots<t^n_{k_n}=T$ of $[0,T]$ such that
--   $$\sup_{0\le i\le k_n-1}|t^n_{i+1}-t^n_i|\xrightarrow[n\to\infty]{}0,\qquad \sup_{u\in[0,T]\setminus\pi^n}|\Delta f(u)|\xrightarrow[n\to\infty]{}0 .$$
--   Then the step functions built from the left endpoints converge uniformly to $f$:
--   $$\sup_{u\in[0,T]}\Big|f(u)-\Big(\sum_{i=0}^{k_n-1}f(t^n_i)\,\mathbf 1_{[t^n_i,t^n_{i+1})}(u)+f(t^n_{k_n})\,\mathbf 1_{\{t^n_{k_n}\}}(u)\Big)\Big|\xrightarrow[n\to\infty]{}0 .$$
--
--   The lemma lets one replace the paths $(X,A)$ by piecewise constant paths along partitions that contain the large jumps of $A$; this is the first step of the proofs of Theorem 2.7 and Theorem 4.1.
--
--   **Formalization Note.** Each "$\sup\to0$" is written as: for every $\varepsilon>0$, eventually the quantity is $\le\varepsilon$ at every point. The page prints "$f(u)-\sum\dots+f(t^n_{k_n})\mathbf 1_{\{t^n_{k_n}\}}(u)$"; the step approximation is the whole bracket, as the proof's definition of $h^n$ shows, and the Lean states the bracketed reading. $\mathbb R^d$ carries the sup norm.
-- source:
--   Cont and Fournié, Functional Itô calculus and stochastic integral representation of martingales, arXiv:1002.2446v5, p. 22, Lemma A.3, (65)

import Mathlib
import Definitions.Def_auto_M05_f3f59_EthierKurtz_HasCrossVariation
import Definitions.Def_FunctionalIto_Formula_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace FunctionalIto.Formula

/-- Lemma A.3 (p. 22), (65): uniform approximation of a cadlag function by step functions.
`π n i` (`i = 0, …, k n`) is a partition `0 = π n 0 < ⋯ < π n (k n) = T` of `[0,T]`; if its
mesh tends to `0` and the jumps of `f` off the partition tend to `0` uniformly, then the step
functions `∑_{i<k_n} f(π n i) 1_{[π n i, π n (i+1))} + f(T) 1_{{T}}` converge to `f`
uniformly on `[0,T]`. Each `sup … → 0` is written `∀ ε > 0, eventually sup ≤ ε`. -/
theorem lemma_A_3 {d : ℕ} (T : ℝ≥0) (f : ℝ≥0 → (Fin d → ℝ)) (hf : CadlagOn T f)
    (k : ℕ → ℕ) (π : ℕ → ℕ → ℝ≥0)
    (h0 : ∀ n, π n 0 = 0) (hT : ∀ n, π n (k n) = T)
    (hmono : ∀ n i, i < k n → π n i < π n (i + 1))
    (hmesh : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ i < k n, (π n (i + 1) : ℝ) - π n i ≤ ε)
    (hjump : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ u ≤ T, (∀ i ≤ k n, u ≠ π n i) →
      ‖f u - Function.leftLim f u‖ ≤ ε) :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ u ≤ T,
      ‖f u - ((∑ i ∈ Finset.range (k n),
          Set.indicator (Set.Ico (π n i) (π n (i + 1))) (fun _ => f (π n i)) u) +
        Set.indicator {π n (k n)} (fun _ => f (π n (k n))) u)‖ ≤ ε := by sorry

end FunctionalIto.Formula
