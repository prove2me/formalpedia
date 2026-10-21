-- Prove2me | Theorems.Thm_ModernConvex_Truss_strict_epigraph_dual_certificate
-- name    : ModernConvex.Truss.strict_epigraph_dual_certificate
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:41.888974+00:00
-- url     : https://prove2.me/theorems/9e3f086a-c432-493d-b929-96727bb5ab08
-- title:
--   Lemma 3.4.2 — dual description of the strict epigraph of the compliance
-- statement:
--   Let $(n, m, B_1, \dots, B_n)$ be a ground structure ($B_i$ an $m \times k_i$ real matrix), $t \in \mathbb R^n$ with $t \ge 0$, $f \in \mathbb R^m$, $\tau \in \mathbb R$, and let $A$, $b$ be the data of the conic quadratic inequality (3.4.49):
--   $$A^T = [\sqrt{2t_1}B_1;\ \sqrt{2t_2}B_2;\ \dots;\ \sqrt{2t_n}B_n;\ -f;\ f], \qquad b^T = [0; \dots; 0;\ -1-\tau;\ -1+\tau],$$
--   and $\mathbf L^k$, $k = \sum_i k_i + 2$, the ice cream cone with the last of these coordinates as its distinguished one. Then the triple $(t, f, \tau)$ belongs to $\mathcal C'$, i.e. $\mathrm{Compl}_f(t) < \tau$, if and only if there is a vector $\lambda$ with
--   $$A^T\lambda = 0, \qquad b^T\lambda > 0, \qquad \lambda \ge_{\mathbf L^k} 0. \qquad (3.4.52)$$
--
--   Writing $\lambda^T = [w_1; \dots; w_n; p; q]$, (3.4.52) reads $\sum_i \sqrt{2t_i}B_iw_i = (p - q)f$, $p(-1-\tau) + q(-1+\tau) > 0$, $\sqrt{\sum_i w_i^Tw_i + p^2} \le q$.
--
--   **Formalization Note** The compliance is `EReal`-valued and compared with the real $\tau$. $\lambda \ge_{\mathbf L^k} 0$ means $\lambda \in \mathbf L^k$.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 126, Lemma 3.4.2

import Mathlib
import Definitions.Def_ModernConvex_Truss_Compliance

open Matrix

namespace ModernConvex.Truss

/-- Ben-Tal–Nemirovski, Lemma 3.4.2, p. 126. A triple `(t, f, τ)` with `t ≥ 0` belongs to `C′`,
i.e. `Compl_f(t) < τ`, iff there exists `λ` with
`Aᵀλ = 0, bᵀλ > 0, λ ≥_{Lᵏ} 0` (3.4.52),
where `A`, `b` are those of (3.4.49): `Aᵀ = [√(2t₁)B₁; …; √(2tₙ)Bₙ; −f; f]`,
`bᵀ = [0; …; 0; −1 − τ; −1 + τ]`, `k = ∑ᵢ kᵢ + 2`. -/
theorem strict_epigraph_dual_certificate {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (t : Fin n → ℝ) (ht : 0 ≤ t)
    (f : Fin m → ℝ) (τ : ℝ) :
    compliance B f t < (τ : EReal) ↔
      ∃ l : CQIIndex k → ℝ, (cqiMatrix B t f)ᵀ *ᵥ l = 0 ∧ 0 < cqiRhs k τ ⬝ᵥ l ∧
        l ∈ lorentzCone ((Σ i, Fin (k i)) ⊕ Unit) := by sorry

end ModernConvex.Truss
