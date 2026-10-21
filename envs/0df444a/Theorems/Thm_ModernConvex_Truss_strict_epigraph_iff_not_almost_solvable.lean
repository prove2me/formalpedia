-- Prove2me | Theorems.Thm_ModernConvex_Truss_strict_epigraph_iff_not_almost_solvable
-- name    : ModernConvex.Truss.strict_epigraph_iff_not_almost_solvable
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:32.095422+00:00
-- url     : https://prove2.me/theorems/a73e38f6-be01-436a-a881-335a1a7e86fe
-- title:
--   (!!) — Compl_f(t) < τ iff the conic quadratic inequality (3.4.48) is not almost solvable
-- statement:
--   Let $(n, m, B_1, \dots, B_n)$ be a ground structure ($B_i$ an $m \times k_i$ real matrix), $t \in \mathbb R^n$ with $t \ge 0$, $f \in \mathbb R^m$ and $\tau \in \mathbb R$. Write the conic quadratic inequality (3.4.48) as
--   $$Av - b \equiv \begin{pmatrix} B(t)v \\ -f^Tv \\ +f^Tv\end{pmatrix} - \begin{pmatrix} 0 \\ -1-\tau \\ -1+\tau\end{pmatrix} \ge_{\mathbf L^k} 0, \qquad (3.4.49)$$
--   where $B(t) = \sqrt2\,[\sqrt{t_1}B_1^T; \dots; \sqrt{t_n}B_n^T]$, $k = \sum_i k_i + 2$, and $\mathbf L^k$ is the ice cream cone whose last coordinate is the last row. Then
--   $$\mathrm{Compl}_f(t) < \tau \iff (3.4.49) \text{ is not almost solvable},$$
--   i.e. the triple $(t, f, \tau)$ lies in the strict epigraph $\mathcal C' = \{(t, f, \tau) : t \ge 0,\ \tau > \mathrm{Compl}_f(t)\}$ exactly when there is an $\varepsilon > 0$ such that no $b'$ with $\|b' - b\|_2 < \varepsilon$ makes $Av - b' \ge_{\mathbf L^k} 0$ solvable.
--
--   **Formalization Note** $\mathrm{Compl}_f(t)$ is `EReal`-valued ($+\infty$ when $A(t)v = f$ has no solution) and is compared with the real $\tau$. Almost solvability is the notion of Proposition 2.4.2(ii).
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 125, statement (!!)

import Mathlib
import Definitions.Def_ModernConvex_Truss_Compliance

open Matrix

namespace ModernConvex.Truss

/-- Ben-Tal–Nemirovski, statement (!!), p. 125. A triple `(t, f, τ)` with `t ≥ 0` belongs to
`C′ = {(t, f, τ) | t ≥ 0, τ > Compl_f(t)}` iff the conic quadratic inequality (3.4.48), written as
`Av − b ≥_{Lᵏ} 0` with the `A`, `b` of (3.4.49), is not almost solvable. -/
theorem strict_epigraph_iff_not_almost_solvable {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (t : Fin n → ℝ) (ht : 0 ≤ t)
    (f : Fin m → ℝ) (τ : ℝ) :
    compliance B f t < (τ : EReal) ↔
      ¬ IsAlmostSolvable (lorentzCone ((Σ i, Fin (k i)) ⊕ Unit)) (cqiMatrix B t f) (cqiRhs k τ) := by sorry

end ModernConvex.Truss
