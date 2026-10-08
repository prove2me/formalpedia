-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_lemma_3
-- name    : ManyServerQED.Scheduling.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:46:58.954387+00:00
-- url     : https://prove2.me/theorems/32efc69b-3683-493e-8361-5a4e6b318866
-- title:
--   Lemma 3 — polynomial moment bound for $\hat X^n$ under work-conserving admissible policies
-- statement:
--   Let Assumptions 1(i) and 3 hold, and let $X^{0,n}\in\mathbb Z^k_+$ have $\hat X^{0,n}=n^{-1/2}(X^{0,n}-\rho n)\to x$. For any sequence of work-conserving admissible policies from these initial states, there are constants $c$ and $\bar m$ independent of the limiting state and policy sequence, and a sequence-dependent threshold $N$, such that
--   $$
--   E\|\hat X^n(t)\|^{m_U}\le c(1+\|x\|^{\bar m})(1+t^{\bar m}),\qquad n\ge N,\ t\ge0.
--   $$
--
--   This supplies a uniform moment estimate for asymptotic cost comparison.
--
--   **Formalization Note** The paper prints the estimate for every $n$ while also saying $c$ is independent of $x$. Its proof uses $\hat X^{0,n}$ in (52). Arbitrary early terms of a sequence converging to $x$ prevent such an all-$n$ uniform bound. The formalization states the eventual estimate with the paper's intended uniform constants. Assumption 2 is unused in the estimate. Expectations are lower Lebesgue integrals.
-- source:
--   Atar, Mandelbaum & Reiman, Scheduling a Multi Class Queue with Many Exponential Servers: Asymptotic Optimality in Heavy Traffic, arXiv:math/0407058v1 (reprint of Ann. Appl. Probab. 14(3), 2004), p. 32, Lemma 3

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ManyServerQED_Scheduling_Policy

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ManyServerQED.Scheduling

/-- Lemma 3 (p. 32), with the uniformity in `x` made explicit. The paper's all-`n` wording
cannot hold uniformly for arbitrary sequences merely converging to `x`: their first term can be
arbitrarily large. The estimate holds eventually, with a threshold depending on the sequence;
the constants `c` and `m̄` depend only on the model and moment exponent, as the page specifies. -/
theorem lemma_3 {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k) (mL mU : ℝ)
    (hA3 : M.Assumption3 mL mU) :
    ∃ (c : ℝ) (mbar : ℕ), ∀ (x : Fin k → ℝ) (X0 : ℕ → Fin k → ℕ),
      Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x) →
      ∀ (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ),
      (∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n) ∧ M.IsAdmissible n (X n) (Ψ n) ∧
        IsWorkConserving n (X n) (Ψ n)) →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t : ℝ, 0 ≤ t →
      ∫⁻ ω, ENNReal.ofReal (l1norm (M.Xhat n (X n) ω t)) ^ mU ∂M.P ≤
        ENNReal.ofReal (c * (1 + l1norm x ^ mbar) * (1 + t ^ mbar)) := by sorry

end ManyServerQED.Scheduling
