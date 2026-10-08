-- Prove2me | Theorems.Thm_HarrisContact_Extinction_eq_7_4
-- name    : HarrisContact.Extinction.eq_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:53:57.133252+00:00
-- url     : https://prove2.me/theorems/02ba81ce-28df-4da1-ac6e-5dd6ab5eba4c
-- title:
--   (7.4), p. 981 — for μ = 1, λ_k = kλ: π₂ − π₁ = (1 + (2d − 1)λ) Σ' r(ξ, ξ ∪ x)(p_∞(ξ ∪ x) − π₂) ≤ (π₂ − π₁)(2d − 1)λ
-- statement:
--   Consider the contact process on $Z_d$ ($d\ge1$) with $\mu=1$ and $\lambda_k=k\lambda$, $\lambda\ge0$, let $r$ be the transition matrix of its imbedded jump chain, and write $\pi_1=p_\infty(\{x\})$, $\pi_2=p_\infty(\xi)$ for a pair of neighbours $\xi=\{x,y\}$. Then
--   $$\pi_2-\pi_1=(1+(2d-1)\lambda)\sum{}'\,r(\xi,\xi\cup z)\,\bigl(p_\infty(\xi\cup z)-\pi_2\bigr)\le(\pi_2-\pi_1)(2d-1)\lambda,$$
--   where $\sum'$ is taken over the sites $z\sim\xi$ outside $\xi$ adjacent to it.
--
--   The equality comes from the first-step equation (7.3) for the pair; the inequality uses the submodularity of Theorem 6.2 in the form $p_\infty(\xi\cup z)-\pi_2\le\pi_2-\pi_1$. Together with (7.2) it yields $(2d-1)\lambda\ge1$ whenever $\pi_1>0$.
--
--   **Formalization Note** The survival probabilities lie in $[0,1]$ and are converted to real numbers so that the differences are ordinary real subtraction. The statement is made for every site $x$ and every neighbour $y$, so the page's $\pi_1$ is $p_\infty(\{x\})$ for the first site of the pair.
-- source:
--   Harris (Ann. Probab. 2, 1974), §7, proof of Theorem 7.1, (7.3)–(7.4), p. 981

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.Extinction

/-- (7.4) (p. 981): with μ = 1 and λ_k = kλ, for a pair of neighbours ξ = {x, y},
π₂ − π₁ = (1 + (2d − 1)λ) Σ'_{z ∼ ξ} r(ξ, ξ ∪ z)(p_∞(ξ ∪ z) − π₂) ≤ (π₂ − π₁)(2d − 1)λ. -/
theorem eq_7_4 {d : ℕ} (hd : 1 ≤ d) (l : ℝ) (hl : 0 ≤ l) :
    ∀ x y : Site d, ∑ i, |x i - y i| = 1 →
      (survInf 1 (fun k => (k : ℝ) * l) {x, y}).toReal
          - (survInf 1 (fun k => (k : ℝ) * l) {x}).toReal =
        (1 + (2 * (d : ℝ) - 1) * l) *
          ∑ z ∈ bdry ({x, y} : Config d),
            jump 1 (fun k => (k : ℝ) * l) {x, y} (insert z {x, y}) *
              ((survInf 1 (fun k => (k : ℝ) * l) (insert z {x, y})).toReal
                - (survInf 1 (fun k => (k : ℝ) * l) {x, y}).toReal) ∧
      (survInf 1 (fun k => (k : ℝ) * l) {x, y}).toReal
          - (survInf 1 (fun k => (k : ℝ) * l) {x}).toReal ≤
        ((survInf 1 (fun k => (k : ℝ) * l) {x, y}).toReal
          - (survInf 1 (fun k => (k : ℝ) * l) {x}).toReal) * ((2 * (d : ℝ) - 1) * l) := by sorry

end HarrisContact.Extinction
