-- Prove2me | Theorems.Thm_ModernConvex_Ellipsoids_inner_sum_sdp
-- name    : ModernConvex.Ellipsoids.inner_sum_sdp
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:34:52.979918+00:00
-- url     : https://prove2.me/theorems/5c8192f4-574a-4a0c-94fc-fab01a1cf9a5
-- title:
--   Proposition 4.9.6 — feasible solutions of (Ĩ) give ellipsoids inside W₁ + ⋯ + W_m of volume ≥ tⁿ
-- statement:
--   Let $A_1,\dots,A_m$ be symmetric positive definite $n\times n$ matrices and $W_i=\{x=A_iu \mid u^Tu\le1\}$. Consider the semidefinite program
--   $$\begin{aligned}&\text{maximize } t\\ &\text{s.t. (a) } t\le\Big(\operatorname{Det}\Big(\tfrac12\sum_{i=1}^m[X_i^TA_i+A_iX_i]\Big)\Big)^{1/n},\\ &\phantom{\text{s.t. }}\text{(b) } \sum_{i=1}^m[X_i^TA_i+A_iX_i]\succeq0,\\ &\phantom{\text{s.t. }}\text{(c) } \begin{pmatrix}I_n&-X_i^T\\-X_i&I_n\end{pmatrix}\succeq0,\ i=1,\dots,m,\end{aligned}\qquad(\tilde I)$$
--   with design variables $X_1,\dots,X_m\in\mathbb R^{n\times n}$ and $t\in\mathbb R$. Then every feasible solution $(\{X_i\},t)$ produces the ellipsoid
--   $$E(X_1,\dots,X_m)=\Big\{x=\Big(\sum_{i=1}^mA_iX_i\Big)u \;\Big|\; u^Tu\le1\Big\},$$
--   contained in the arithmetic sum $W_1+\dots+W_m$, and its normalized volume is at least $t^n$. The largest-volume ellipsoid obtainable in this way comes from any optimal solution: if $(\{X^*_i\},t^*)$ is optimal for $(\tilde I)$ (feasible, and no feasible solution has larger $t$) and $(\{X_i\},t)$ is feasible, then $\operatorname{Vol}(E(X_1,\dots,X_m))\le\operatorname{Vol}(E(X^*_1,\dots,X^*_m))$.
--
--   This is the statement as printed. For $n$ even and $t<0$ the volume clause fails. Constraint (a) admits every $t\le0$: the solution $n=2$, $m=1$, $A_1=I$, $X_1=0$, $t=-10$ is feasible, its ellipsoid is $\{0\}$ of volume $0$, and $t^n=100$. A corrected variant adds $t\ge0$.
--
--   **Formalization Note** Normalized volume is Lebesgue measure divided by that of the unit Euclidean ball, valued in $[0,\infty]$. The bound $t^n$ is a natural-number power embedded as a nonnegative extended real. For odd $n$ and $t<0$ both the book's real inequality and the Lean one are trivially true. $\operatorname{Det}^{1/n}$ is a real power of a nonnegative determinant. The book's closing sentence ("the largest-volume ellipsoid which can be obtained in this way is associated with (any) optimal solution") is the second conjunct: the ellipsoid of any optimal solution has volume at least that of the ellipsoid of every feasible solution. Existence of an optimal solution is not asserted.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, pp. 273–274, Proposition 4.9.6

import Mathlib
import Definitions.Def_ModernConvex_Ellipsoids_Ellipsoid
import Definitions.Def_ModernConvex_Ellipsoids_Programs

open Matrix

namespace ModernConvex.Ellipsoids

/-- Ben-Tal–Nemirovski, Proposition 4.9.6, pp. 273–274. Let \`Wᵢ = {x = Aᵢu | uᵀu ≤ 1}\`,
\`Aᵢ ≻ 0\`, \`i = 1, …, m\`, and consider the semidefinite program (Ĩ): maximize \`t\` s.t.
(a) \`t ≤ (Det(½ Σᵢ [XᵢᵀAᵢ + AᵢXᵢ]))^{1/n}\`, (b) \`Σᵢ [XᵢᵀAᵢ + AᵢXᵢ] ⪰ 0\`,
(c) \`( Iₙ −Xᵢᵀ ; −Xᵢ Iₙ ) ⪰ 0\`, with design variables \`X₁, …, X_m ∈ M^{n,n}\`, \`t ∈ ℝ\`.
Every feasible solution `({Xᵢ}, t)` produces the ellipsoid
`E(X₁, …, X_m) = {x = (Σᵢ AᵢXᵢ)u | uᵀu ≤ 1}` contained in `W₁ + ⋯ + W_m`, and the (normalized)
volume of this ellipsoid is at least `tⁿ`. The largest-volume ellipsoid which can be obtained in
this way is associated with (any) optimal solution to (Ĩ). (As printed; see FINDINGS.yaml F1:
the volume clause is false for `n` even and `t < 0`.) -/
theorem inner_sum_sdp {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).PosDef) :
    (∀ (X : Fin m → Matrix (Fin n) (Fin n) ℝ) (t : ℝ), IFeasible A X t →
      ellipsoid (∑ i, A i * X i) 0 ⊆ minkowskiSum (fun i => ellipsoid (A i) 0) ∧
        ENNReal.ofReal (t ^ n) ≤ Vol (ellipsoid (∑ i, A i * X i) 0)) ∧
    (∀ (Xs : Fin m → Matrix (Fin n) (Fin n) ℝ) (ts : ℝ), IOptimal A Xs ts →
      ∀ (X : Fin m → Matrix (Fin n) (Fin n) ℝ) (t : ℝ), IFeasible A X t →
        Vol (ellipsoid (∑ i, A i * X i) 0) ≤ Vol (ellipsoid (∑ i, A i * Xs i) 0)) := by sorry

end ModernConvex.Ellipsoids
