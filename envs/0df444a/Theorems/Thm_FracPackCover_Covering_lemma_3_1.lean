-- Prove2me | Theorems.Thm_FracPackCover_Covering_lemma_3_1
-- name    : FracPackCover.Covering.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:46:50.14965+00:00
-- url     : https://prove2.me/theorems/6789a4d4-6b49-4323-9ce6-d14543cf0b06
-- title:
--   Lemma 3.1 — 𝒞1 and 𝒞2 certify infeasibility when $\lambda\le1-3\varepsilon$, and $3\varepsilon$-optimality otherwise
-- statement:
--   Let $A\ge0$, $b>0$ and a nonempty convex $P$ in the nonnegative orthant be covering data, and let $0<\varepsilon<\frac13$. Let $x\in P$ with $\lambda=\lambda(x)=\min_i a_ix/b_i$, and let $y\ge0$, $y\ne0$. Let $\tilde x\in P$ maximize $y^tAx$ over $P$ and put $C_{\mathcal C}(y)=y^tA\tilde x$. Suppose that $(x,\lambda)$ and $y$ satisfy the relaxed optimality conditions
--   $$(1+\varepsilon)\lambda\,y^tb\ge y^tAx,\qquad C_{\mathcal C}(y)-y^tAx\le\varepsilon\,(C_{\mathcal C}(y)+y^tb).$$
--   Then:
--   1. if $\lambda\le1-3\varepsilon$, there is no exact solution, i.e. no $x'\in P$ with $Ax'\ge b$;
--   2. if $\lambda\ge1-3\varepsilon$, then $x$ is $3\varepsilon$-optimal: $(1-3\varepsilon)\lambda(x')\le\lambda$ for every $x'\in P$.
--
--   This lemma turns the two relaxed optimality conditions into the two outcomes of the covering algorithm: a certificate that no exact solution exists, or a near-optimal point from which $\varepsilon$-scaling continues.
--
--   **Formalization Note** "$x$ is $3\varepsilon$-optimal", i.e. $\lambda\ge(1-3\varepsilon)\lambda^*$ with $\lambda^*=\max\{\lambda(x'):x'\in P\}$ the value of (8), is stated without $\lambda^*$ as the inequality for every $x'\in P$. The hypotheses $y\ne0$ and $\varepsilon<\frac13$ are implicit in the paper: for $y=0$ both conditions hold and both conclusions can fail, and the proof divides by $1-3\varepsilon$. The algorithm uses the lemma with $\varepsilon\le\frac16$.
-- source:
--   Plotkin, Shmoys, Tardos, Fast Approximation Algorithms for Fractional Packing and Covering Problems, Cornell ORIE Tech. Rep. 999 (1992), pp. 17–18, Lemma 3.1

import Mathlib
import Definitions.Def_FracPackCover_Covering_Basic

namespace FracPackCover.Covering

/-- Lemma 3.1 (Plotkin–Shmoys–Tardos, Cornell ORIE TR 999, p. 17). Let `(x, λ)` with `x ∈ P`,
`λ = λ(x)`, and `y ≥ 0`, `y ≠ 0` be feasible primal and dual solutions satisfying 𝒞1 and 𝒞2, where
`C_𝒞(y) = yᵗ A x̃` for a maximizer `x̃ ∈ P` of `yᵗ A x` over `P`. If `λ ≤ 1 − 3ε` there is no exact
solution; if `λ ≥ 1 − 3ε`, `x` is `3ε`-optimal: `(1 − 3ε) λ(x') ≤ λ` for every `x' ∈ P`.
The hypotheses `y ≠ 0` and `0 < ε < 1/3` are implicit in the paper's proof. -/
theorem lemma_3_1 {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hdata : IsCoveringData A b P)
    (ε : ℝ) (hε : 0 < ε) (hε3 : ε < 1 / 3)
    (x : Fin n → ℝ) (hx : x ∈ P) (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i) (hy0 : y ≠ 0)
    (xt : Fin n → ℝ) (hxt : xt ∈ P) (hmax : ∀ x' ∈ P, yAx A y x' ≤ yAx A y xt)
    (hC1 : C1 A b ε (lam A b x) y x) (hC2 : C2 A b ε y x (yAx A y xt)) :
    (lam A b x ≤ 1 - 3 * ε → ¬ ∃ x' ∈ P, ∀ i, b i ≤ rowVal A x' i) ∧
    (1 - 3 * ε ≤ lam A b x → ∀ x' ∈ P, (1 - 3 * ε) * lam A b x' ≤ lam A b x) := by sorry

end FracPackCover.Covering
