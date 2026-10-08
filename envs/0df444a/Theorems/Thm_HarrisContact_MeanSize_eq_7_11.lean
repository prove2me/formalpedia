-- Prove2me | Theorems.Thm_HarrisContact_MeanSize_eq_7_11
-- name    : HarrisContact.MeanSize.eq_7_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:27:13.664894+00:00
-- url     : https://prove2.me/theorems/75025b15-fc95-4cd1-ab37-e62705a2d9e4
-- title:
--   (7.11), p. 982 — $M_2(T)-M_1(T) \le 1/(1-(2d-1)\lambda)$
-- statement:
--   Take death rate $\mu=1$ and birth rates $\lambda_k=k\lambda$ on $Z_d$, $d\ge1$, with $\lambda\ge0$ and $(2d-1)\lambda<1$. Let $x,y$ be neighbours, and for $T\ge0$ let
--   $$M_1(T)=\int_0^T m_s(\{x\})\,ds,\qquad M_2(T)=\int_0^T m_s(\{x,y\})\,ds .$$
--   Then $M_1(T)$ and $M_2(T)$ are finite,
--   $$M_2(T)-M_1(T)\le 1+(2d-1)\lambda\,\big(M_2(T)-M_1(T)\big),\qquad(7.11)$$
--   and consequently
--   $$M_2(T)-M_1(T)\le\frac{1}{1-(2d-1)\lambda},\qquad T\ge0.$$
--
--   The uniform bound in $T$ is what, combined with Lemma 7.5, shows that $\int_0^\infty m_t\,dt<\infty$ for a singleton.
--
--   **Formalization Note** The integrals are Lebesgue integrals of $[0,\infty]$-valued functions; the finiteness conjuncts (the paper's "bounded on each finite $t$-interval", from Lemma 4.7) make the real-valued differences meaningful. The process is the countable-state chain on finite configurations of §4 (p. 975), with transition function the minimal solution $P_t$ of the backward equations for the rates (4.4)–(4.5); $m_t(\xi)=\sum_\eta P_t(\xi,\eta)\,|\eta|$ is an extended nonnegative real, so a divergent sum is $+\infty$, never $0$.
-- source:
--   Harris (Ann. Probab. 2, 1974), §7, proof of Theorem 7.6, (7.11) and the display after it, p. 982

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.MeanSize

/-- Harris (Ann. Probab. 2, 1974), (7.11) and the bound after it, p. 982: for `μ = 1`, `λ_k = kλ` with
`(2d − 1)λ < 1`, a pair of neighbours `{x, y}`, `M_1(T) = ∫_0^T m_s({x}) ds` and
`M_2(T) = ∫_0^T m_s({x, y}) ds`: both are finite,
`M_2(T) − M_1(T) ≤ 1 + (2d − 1)λ (M_2(T) − M_1(T))` and `M_2(T) − M_1(T) ≤ 1/(1 − (2d − 1)λ)`. -/
theorem eq_7_11 {d : ℕ} (hd : 1 ≤ d) (l : ℝ) (hl : 0 ≤ l) (hsub : (2 * (d : ℝ) - 1) * l < 1)
    (x y : HarrisContact.Extinction.Site d) (hxy : y ∈ HarrisContact.Extinction.nbrs x) (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ s in Set.Icc 0 T, HarrisContact.Extinction.meanSize 1 (fun k => (k : ℝ) * l) s ({x, y} : HarrisContact.Extinction.Config d)) < ∞ ∧
    (∫⁻ s in Set.Icc 0 T, HarrisContact.Extinction.meanSize 1 (fun k => (k : ℝ) * l) s ({x} : HarrisContact.Extinction.Config d)) < ∞ ∧
    (∫⁻ s in Set.Icc 0 T, HarrisContact.Extinction.meanSize 1 (fun k => (k : ℝ) * l) s ({x, y} : HarrisContact.Extinction.Config d)).toReal -
        (∫⁻ s in Set.Icc 0 T, HarrisContact.Extinction.meanSize 1 (fun k => (k : ℝ) * l) s ({x} : HarrisContact.Extinction.Config d)).toReal ≤
      1 + (2 * (d : ℝ) - 1) * l *
        ((∫⁻ s in Set.Icc 0 T, HarrisContact.Extinction.meanSize 1 (fun k => (k : ℝ) * l) s ({x, y} : HarrisContact.Extinction.Config d)).toReal -
          (∫⁻ s in Set.Icc 0 T, HarrisContact.Extinction.meanSize 1 (fun k => (k : ℝ) * l) s ({x} : HarrisContact.Extinction.Config d)).toReal) ∧
    (∫⁻ s in Set.Icc 0 T, HarrisContact.Extinction.meanSize 1 (fun k => (k : ℝ) * l) s ({x, y} : HarrisContact.Extinction.Config d)).toReal -
        (∫⁻ s in Set.Icc 0 T, HarrisContact.Extinction.meanSize 1 (fun k => (k : ℝ) * l) s ({x} : HarrisContact.Extinction.Config d)).toReal ≤
      1 / (1 - (2 * (d : ℝ) - 1) * l) := by sorry
end HarrisContact.MeanSize
