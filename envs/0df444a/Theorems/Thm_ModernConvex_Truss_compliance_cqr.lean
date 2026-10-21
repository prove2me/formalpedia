-- Prove2me | Theorems.Thm_ModernConvex_Truss_compliance_cqr
-- name    : ModernConvex.Truss.compliance_cqr
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:43.37416+00:00
-- url     : https://prove2.me/theorems/b9dd7e85-f5af-4fdd-a9d5-ff6900f34935
-- title:
--   Proposition 3.4.5 — the compliance of a truss is conic quadratic representable
-- statement:
--   Let $(n, m, B_1, \dots, B_n)$ be a ground structure, $B_i$ an $m \times k_i$ real matrix, and let $\mathrm{Compl}_f(t)$ be the compliance of the truss $t$ under the load $f$ — $\tfrac12 f^Tv$ for a solution $v$ of $A(t)v = f$, $A(t) = \sum_i t_iB_iB_i^T$, and $+\infty$ if there is none — extended by the value $+\infty$ to the $t \in \mathbb R^n$ that are not nonnegative.
--
--   1. For all $t \in \mathbb R^n$, $f \in \mathbb R^m$, $\tau \in \mathbb R$: the triple $(t, f, \tau)$ belongs to the epigraph of $\mathrm{Compl}_f(t)$, i.e. $\mathrm{Compl}_f(t) \le \tau$, if and only if there exist vectors $s_i \in \mathbb R^{k_i}$, $i = 1, \dots, n$, such that
--   $$\text{(a)}\ \sum_{i=1}^n B_is_i = f, \qquad \text{(b)}\ \sum_{i=1}^n \frac{s_i^Ts_i}{2t_i} \le \tau, \qquad \text{(c)}\ t \ge 0, \qquad (3.4.56)$$
--   with the convention $0/0 = 0$ and $a/0 = +\infty$ for $a > 0$.
--   2. In particular, the function $(t, f) \mapsto \mathrm{Compl}_f(t)$ is conic quadratic representable: its epigraph $\{(t, f, \tau) : \mathrm{Compl}_f(t) \le \tau\} \subset \mathbb R^n \times \mathbb R^m \times \mathbb R$ is the projection of the solution set of finitely many conic quadratic inequalities $A_j(t, f, \tau; u) - b_j \ge_{\mathbf L^{m_j}} 0$ in $(t, f, \tau)$ and additional variables $u$.
--
--   This explicit representation lets truss topology design problems with compliance constraints (multiload, bounds on bar volumes) be written as conic quadratic programs.
--
--   **Formalization Note** The compliance is `EReal`-valued. Condition (b) with the convention $0/0 = 0$, $a/0 = +\infty$ is encoded as: $s_i = 0$ whenever $t_i = 0$, and $\sum_i s_i^Ts_i/(2t_i) \le \tau$ with Lean's real division, under which the terms with $t_i = 0$ are $0$; without the first clause Lean's $x/0 = 0$ would make (b) too weak. Condition (c) is part of the equivalence, not a hypothesis. "CQr" is the book's definition of p. 86–87 (cones $\mathbf L^{m_j}$ with $m_j \ge 2$), applied to the function of $(t, f) \in \mathbb R^{n+m}$.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 127, Proposition 3.4.5

import Mathlib
import Definitions.Def_ModernConvex_Truss_Compliance

open Matrix

namespace ModernConvex.Truss

/-- Ben-Tal–Nemirovski, Proposition 3.4.5, p. 127. A triple `(t, f, τ)` belongs to the epigraph of
`Compl_f(t)` extended by `+∞` to the `t`'s that are not nonnegative, i.e. `Compl_f(t) ≤ τ`, iff there
are vectors `sᵢ ∈ ℝ^{kᵢ}`, `i = 1, …, n`, with
(a) `∑ᵢ Bᵢsᵢ = f`, (b) `∑ᵢ sᵢᵀsᵢ / (2tᵢ) ≤ τ`, (c) `t ≥ 0` (3.4.56),
under the convention `0/0 = 0`, `a/0 = +∞` for `a > 0` (encoded as `tᵢ = 0 → sᵢ = 0` together with
Lean's `x / 0 = 0`). In particular, the function `(t, f) ↦ Compl_f(t)` is CQr. -/
theorem compliance_cqr {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) :
    (∀ (t : Fin n → ℝ) (f : Fin m → ℝ) (τ : ℝ),
      extendedCompliance B f t ≤ (τ : EReal) ↔
        ∃ s : (i : Fin n) → Fin (k i) → ℝ,
          -- (a)
          ∑ i, B i *ᵥ s i = f ∧
          -- (b)
          ((∀ i, t i = 0 → s i = 0) ∧ ∑ i, (s i ⬝ᵥ s i) / (2 * t i) ≤ τ) ∧
          -- (c)
          0 ≤ t) ∧
    IsCQrFunction (fun x : Fin n ⊕ Fin m → ℝ =>
      extendedCompliance B (fun j => x (Sum.inr j)) (fun i => x (Sum.inl i))) := by sorry

end ModernConvex.Truss
