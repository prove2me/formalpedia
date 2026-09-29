-- Prove2me | Theorems.Thm_KannanLattice_Core_closest_point_tail_mem_candidates
-- name    : KannanLattice.Core.closest_point_tail_mem_candidates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:14:26.265737+00:00
-- url     : https://prove2.me/theorems/e2a954dd-8655-4f09-aaa1-61dfc4912dbb
-- title:
--   Proposition 4.3 — the tail of a closest lattice point lies in an explicit set of ≤ n^{n−i+1} candidates
-- statement:
--   Let $m\ge2$, let $b_1,\dots,b_m$ be a reduced basis (Definition 2.6) of a lattice $L\subseteq\mathcal R^k$, let $b_0\in\mathcal R^k$, let $\bar b_0$ be its orthogonal projection onto $\operatorname{span}\{b_1,\dots,b_m\}$, and let $i$ be an index with $b_i(i)=\max_j b_j(j)$. Write $P_i$ for the orthogonal projection onto the orthogonal complement of $\operatorname{span}\{b_1,\dots,b_{i-1}\}$ and let
--
--   $$T=\Big\{(\mu_i,\dots,\mu_m)\in\mathbb Z^{m-i+1} : \Big|P_i\Big(\sum_{j=i}^m\mu_jb_j-\bar b_0\Big)\Big|\le\frac{\sqrt m}{2}\,b_i(i)\Big\}.$$
--
--   Then $T$ is finite,
--
--   $$|T|\le m^{\,m-i+1},$$
--
--   and whenever $\sum_{j=1}^m\lambda_jb_j$ ($\lambda_j\in\mathbb Z$) is a closest point of $L$ to $b_0$, the tail $(\lambda_i,\dots,\lambda_m)$ belongs to $T$.
--
--   This is the enumeration bound of the closest-vector procedure CLP′: only $m^{m-i+1}$ tails need to be tried, each followed by a recursive call in dimension $i-1$.
--
--   **Formalization Note** (1) The paper says "there exists an easily determined set $T$"; an existential $T$ would be satisfied by the set of tails of closest points and lose the content, so the explicit set of the paper's proof is stated instead. (2) The paper's statement fails for $n=1$ ($L=\mathbb Z$, $b_0=\tfrac12$: two closest points, $|T|\le1$); the procedure CLP′ handles $n=1$ separately, so $m\ge2$ is assumed. (3) Reducedness and the maximality of $b_i(i)$ are the standing assumptions of CLP′ ("assumes that the input basis is reduced in the sense of (2.7) and (2.8)", p. 23). (4) Indices are 0-based in Lean: the bound is `m ^ (m - i)` with 0-based `i`, the paper's $n^{n-i+1}$ with 1-based $i$; tails are functions on `{j : Fin m // i ≤ j}`.
-- source:
--   Kannan, Minkowski's Convex Body Theorem and Integer Programming, Math. Oper. Res. 12 (1987); author's final manuscript (CMU-CS-96-105), pp. 23–24, Proposition 4.3 and its proof (explicit T, n ≥ 2); p. 23, procedure CLP′ (reduced input basis)

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_KannanLattice_Core_IsReduced

namespace KannanLattice.Core

/-- Proposition 4.3 of Kannan (1987), pp. 23–24, with the proof's explicit candidate set `T` and
`m ≥ 2`. Let `b` be a reduced basis (Definition 2.6) of a lattice in `ℝᵏ`, `b₀ ∈ ℝᵏ`, `b̄₀` its
projection onto `span_ℝ(b)`, and `i` an index with `b_i(i) = max_j b_j(j)`. Let `T` be the set of
integer tails `μ = (μ_j)_{j ≥ i}` with `|P_i(Σ_{j ≥ i} μ_j b_j − b̄₀)| ≤ (√m/2) b_i(i)`, where `P_i`
projects orthogonally to `span(b_j : j < i)`. Then `T` is finite with at most `m^{m−i}` elements
(0-based `i`; the paper's `n^{n−i+1}`), and the tail of the coefficient vector of every closest
lattice point to `b₀` lies in `T`. -/
theorem closest_point_tail_mem_candidates (m k : ℕ) (hm : 2 ≤ m)
    (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b) (hred : IsReduced b)
    (b₀ : EuclideanSpace ℝ (Fin k)) (i : Fin m) (hi : ∀ j : Fin m, gsLen b j ≤ gsLen b i) :
    let T : Set ({j : Fin m // i ≤ j} → ℤ) :=
      {μ | ‖projOrth b i ((∑ j : {j : Fin m // i ≤ j}, (μ j : ℝ) • b j) -
              (Submodule.span ℝ (Set.range b)).starProjection b₀)‖ ≤
            Real.sqrt m / 2 * gsLen b i}
    T.Finite ∧ T.ncard ≤ m ^ (m - (i : ℕ)) ∧
      ∀ lam : Fin m → ℤ,
        (∀ w ∈ lattice b, ‖(∑ j, (lam j : ℝ) • b j) - b₀‖ ≤ ‖w - b₀‖) →
          (fun j : {j : Fin m // i ≤ j} => lam j) ∈ T := by sorry

end KannanLattice.Core
