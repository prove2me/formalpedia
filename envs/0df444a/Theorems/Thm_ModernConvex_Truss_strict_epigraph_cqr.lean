-- Prove2me | Theorems.Thm_ModernConvex_Truss_strict_epigraph_cqr
-- name    : ModernConvex.Truss.strict_epigraph_cqr
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:34.123688+00:00
-- url     : https://prove2.me/theorems/fd9ce640-984c-4082-b7a8-f6a743a00d7f
-- title:
--   Lemma 3.4.3 — Compl_f(t) < τ iff Σ Bᵢsᵢ = f and Σ sᵢᵀsᵢ/(2tᵢ) < τ for some sᵢ
-- statement:
--   Let $(n, m, B_1, \dots, B_n)$ be a ground structure ($B_i$ an $m \times k_i$ real matrix), $t \in \mathbb R^n$ with $t \ge 0$, $f \in \mathbb R^m$ and $\tau \in \mathbb R$. Then $\mathrm{Compl}_f(t) < \tau$ if and only if there exist vectors $s_i \in \mathbb R^{k_i}$, $i = 1, \dots, n$, with
--   $$\sum_{i=1}^n B_is_i = f, \qquad \sum_{i=1}^n \frac{s_i^Ts_i}{2t_i} < \tau, \qquad (3.4.55)$$
--   where, by definition, $0/0 = 0$ and $a/0 = +\infty$ for $a > 0$.
--
--   **Formalization Note** The convention $0/0 = 0$, $a/0 = +\infty$ is encoded by requiring $s_i = 0$ whenever $t_i = 0$ (a term $a/0$ with $a > 0$ would make the sum $+\infty$, which is never $< \tau$), and by summing $s_i^Ts_i/(2t_i)$ with Lean's real division, under which the terms with $t_i = 0$ (and hence $s_i = 0$) are $0$. Without the clause $t_i = 0 \Rightarrow s_i = 0$, Lean's convention $x/0 = 0$ would let a missing bar carry any force. The compliance is `EReal`-valued and compared with the real $\tau$.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 127, Lemma 3.4.3

import Mathlib
import Definitions.Def_ModernConvex_Truss_Compliance

open Matrix

namespace ModernConvex.Truss

/-- Ben-Tal–Nemirovski, Lemma 3.4.3, p. 127. A triple `(t ≥ 0, f, τ)` has `Compl_f(t) < τ` iff there
are vectors `sᵢ ∈ ℝ^{kᵢ}`, `i = 1, …, n`, with
`∑ᵢ Bᵢsᵢ = f` and `∑ᵢ sᵢᵀsᵢ / (2tᵢ) < τ` (3.4.55),
under the convention `0/0 = 0`, `a/0 = +∞` for `a > 0`: a term with `tᵢ = 0` is finite only when
`sᵢ = 0`, and then it is `0` (here: `tᵢ = 0 → sᵢ = 0`, and Lean's `x / 0 = 0` gives the `0`). -/
theorem strict_epigraph_cqr {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (t : Fin n → ℝ) (ht : 0 ≤ t)
    (f : Fin m → ℝ) (τ : ℝ) :
    compliance B f t < (τ : EReal) ↔
      ∃ s : (i : Fin n) → Fin (k i) → ℝ,
        ∑ i, B i *ᵥ s i = f ∧
        (∀ i, t i = 0 → s i = 0) ∧
        ∑ i, (s i ⬝ᵥ s i) / (2 * t i) < τ := by sorry

end ModernConvex.Truss
