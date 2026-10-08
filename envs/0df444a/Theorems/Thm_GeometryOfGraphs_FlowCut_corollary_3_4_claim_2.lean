-- Prove2me | Theorems.Thm_GeometryOfGraphs_FlowCut_corollary_3_4_claim_2
-- name    : GeometryOfGraphs.FlowCut.corollary_3_4_claim_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:43:49.850373+00:00
-- url     : https://prove2.me/theorems/ee368fc2-c3f7-4d72-af9e-abc373e13edf
-- title:
--   Corollary 3.4, Claim 2 (p. 223) — a non-expanding ℓ₁ embedding that shrinks every terminal pair by at most O(log k)
-- statement:
--   There is an absolute constant $C_1 > 0$ with the following property. Let $(X, d)$ be a finite semi-metric space and let $(s_1, t_1), \dots, (s_k, t_k)$ be $k$ pairs of points of $X$. Then for some $m$ there is a map $\varphi : X \to \mathbb R^m$ such that, with $\|\cdot\|_1$ the $\ell_1$ norm,
--   $$\|\varphi(x) - \varphi(y)\|_1 \le d(x,y)\quad\text{for all } x, y \in X,$$
--   $$d(s_i, t_i) \le C_1 \log(\max(k,2))\,\|\varphi(s_i) - \varphi(t_i)\|_1 \quad\text{for } i = 1, \dots, k.$$
--
--   So $\varphi$ never expands distances, and contracts each of the $k$ designated pairs by a factor at most $O(\log k)$, regardless of the number of points of $X$. This is a terminal version of Bourgain's embedding theorem; it is what produces the factor $\log k$ in Theorem 4.1. Claim 1 of the same corollary is the randomized version with the terminal set $Y$; the proof of Theorem 4.1 uses Claim 2.
--
--   **Formalization Note** The paper states the existence of a deterministic polynomial-time algorithm that finds $\varphi$ with target $\ell_1^{O(n^2)}$. The statement asserts only the existence of $\varphi$, into $\ell_1^m$ for some $m$: the algorithm and the dimension bound are not stated. The paper writes $\Omega(1/\log k)$; the statement asserts an absolute constant $C_1$, quantified before $X$, $d$ and the pairs. $\log(\max(k,2))$ replaces $\log k$, which vanishes at $k = 1$. The space $X$ is any finite type in `Type`; the metric is a semi-metric (p. 218, footnote 1).
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 223, Corollary 3.4, Claim 2

import Mathlib
import Definitions.Def_GeometryOfGraphs_FlowCut_Pseudometric

set_option autoImplicit false

namespace GeometryOfGraphs.FlowCut

/-- Corollary 3.4, Claim 2 (p. 223), existence form: there is an absolute constant `C₁ > 0` such that
every finite (semi-)metric space `(X, d)` with `k` pairs `(s i, t i)` admits a map `φ` into some
`ℓ₁^m` that is non-expanding (`‖φ x - φ y‖₁ ≤ d x y`) and shrinks every pair by a factor at most
`C₁ * log (max k 2)`. The algorithm and the dimension `O(n²)` of the printed claim are not stated. -/
theorem corollary_3_4_claim_2 :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ (X : Type) [Fintype X] (d : X → X → ℝ), IsPseudometric d →
        ∀ (k : ℕ) (s t : Fin k → X),
          ∃ (m : ℕ) (φ : X → Fin m → ℝ),
            (∀ x y, ∑ r, |φ x r - φ y r| ≤ d x y) ∧
            ∀ i, d (s i) (t i) ≤ C₁ * Real.log (max (k : ℝ) 2) * ∑ r, |φ (s i) r - φ (t i) r| := by sorry

end GeometryOfGraphs.FlowCut
