-- Prove2me | Theorems.Thm_MartOT_Var_case_two_cannot_occur
-- name    : MartOT.Var.case_two_cannot_occur
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:36.905638+00:00
-- url     : https://prove2.me/theorems/f1ec1cb9-c38f-40f3-a8dc-5d855b01662b
-- title:
--   Proof of Lemma 1.11, pp. 18–19 — for an optimal π of finite cost, case (2) of Theorem 3.1 cannot occur
-- statement:
--   Let $\mu,\nu$ be probability measures on $\mathbb R$ in convex order, $c:\mathbb R^2\to\mathbb R$ a Borel cost satisfying the sufficient integrability condition, and $\pi\in\Pi_M(\mu,\nu)$ an optimal martingale transport plan with $\int c\,d\pi<+\infty$. Fix $n\in\mathbb N$ and let $M\subseteq(\mathbb R^2)^n$ be the set of $n$-tuples carrying a finite measure that some competitor beats. Then there is **no** measure $\gamma$ on $(\mathbb R^2)^n$ with
--   $$\gamma(M)>0\qquad\text{and}\qquad\operatorname{proj}^i_{\#}\gamma\le\pi\quad(i=1,\dots,n).$$
--
--   Together with Theorem 3.1 this forces case (1), which yields the set $\Gamma_n$.
--
--   **Formalization Note** $(\mathbb R^2)^n$ is `Fin n → ℝ × ℝ`; $M$ is the definition `BadTuples`.
-- source:
--   arXiv:1208.1509v2, §3, proof of Lemma 1.11, pp. 18–19 ("It remains to show that case (2) cannot occur.")

import Mathlib
import Definitions.Def_MartOT_Var_BadTuples

namespace MartOT.Var

open MeasureTheory

theorem case_two_cannot_occur (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : ConvexLE μ ν) (c : ℝ → ℝ → ℝ)
    (hc : Measurable (Function.uncurry c)) (hint : SuffIntegrable μ ν c)
    (π : Measure (ℝ × ℝ)) (hπ : IsOptimal c μ ν π) (hfin : cost c π < ⊤) (n : ℕ) :
    ¬ ∃ γ : Measure (Fin n → ℝ × ℝ), 0 < γ (BadTuples c n) ∧
        ∀ i, γ.map (fun z : Fin n → ℝ × ℝ => z i) ≤ π := by sorry

end MartOT.Var
