-- Prove2me | Theorems.Thm_OptimalBAI_ChernoffPAC_kt_ratio_bound
-- name    : OptimalBAI.ChernoffPAC.kt_ratio_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T02:02:37.447592+00:00
-- url     : https://prove2.me/theorems/81997beb-7652-4f11-8ac2-3197dc55b531
-- title:
--   Lemma 11 — the Krichevsky–Trofimov distribution is a probability law within a factor 2√n of the maximum likelihood
-- statement:
--   For $x \in \{0,1\}^n$ and $u \in [0,1]$ let $p_u(x) = \prod_i u^{x_i}(1-u)^{1-x_i}$ be the likelihood of the successive observations $x$ of a Bernoulli random variable with mean $u$, and let
--
--   $$\mathrm{kt}(x) = \int_0^1 \frac{1}{\pi\sqrt{u(1-u)}}\, p_u(x)\,\mathrm du$$
--
--   be the Krichevsky–Trofimov distribution. Then:
--
--   1. $\mathrm{kt}$ is a probability law on $\{0,1\}^n$: $\mathrm{kt}(x) \ge 0$ for all $x$ and $\sum_{x \in \{0,1\}^n} \mathrm{kt}(x) = 1$;
--   2. if $n \ge 1$, then for every $x \in \{0,1\}^n$ and every $u \in [0,1]$,
--
--   $$p_u(x) \le 2\sqrt n\ \mathrm{kt}(x), \qquad\text{equivalently}\qquad \sup_{x\in\{0,1\}^n}\ \sup_{u\in[0,1]} \frac{p_u(x)}{\mathrm{kt}(x)} \le 2\sqrt n .$$
--
--   The lemma is due to Willems, Shtarkov and Tjalkens (1995); the paper quotes it without proof. It is the tool that turns the maximum likelihood in the numerator of the GLR statistic into a genuine mixture density, at a cost of a factor $2\sqrt n$ per arm, in the proof of Theorem 10.
--
--   **Formalization Note** The bound is stated multiplicatively, which avoids dividing by $\mathrm{kt}(x)$; since $\mathrm{kt}(x) > 0$ this is equivalent to the printed ratio form (and the multiplicative form itself forces $\mathrm{kt}(x) > 0$, as $p_{1/2}(x) > 0$). The hypothesis $n \ge 1$ is **added**: at $n = 0$ the ratio is $p_u(\emptyset)/\mathrm{kt}(\emptyset) = 1 > 0 = 2\sqrt 0$, so the printed bound fails there. The probability-law part is stated for all $n$, including $n = 0$ where $\mathrm{kt}(\emptyset) = 1$.
-- source:
--   Garivier, Kaufmann, Optimal Best Arm Identification with Fixed Confidence, arXiv:1602.04589v2, pp. 10–11, Lemma 11 [Willems et al. (1995)]

import Mathlib
import Definitions.Def_OptimalBAI_ChernoffPAC_KrichevskyTrofimov

namespace OptimalBAI.ChernoffPAC

theorem kt_ratio_bound (n : ℕ) :
    (∀ x : Fin n → Bool, 0 ≤ ktProb x) ∧
    (∑ x : Fin n → Bool, ktProb x) = 1 ∧
    (1 ≤ n → ∀ x : Fin n → Bool, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      bernSeqLik u x ≤ 2 * Real.sqrt n * ktProb x) := by sorry

end OptimalBAI.ChernoffPAC
