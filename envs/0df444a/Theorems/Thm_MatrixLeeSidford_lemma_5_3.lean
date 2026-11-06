-- Prove2me | Theorems.Thm_MatrixLeeSidford_lemma_5_3
-- name    : MatrixLeeSidford.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:31:12.953426+00:00
-- url     : https://prove2.me/theorems/fd50624f-96dc-4308-9b13-1f140fa239fb
-- title:
--   Lemma 5.3 — curvature along a matrix exponential curve
-- statement:
--   Let $B$ be a real $a\times b$ matrix, $L\in\mathbb S^a$ and $R\in\mathbb S^b$, and $s\ge1$ an integer. Define
--   $$
--   B(t)=e^{tL}Be^{tR},\qquad u(t)=\frac1s\operatorname{tr}\big[(B(t)B(t)^\top)^s\big],
--   $$
--   and, at a time $t$, $D=B(t)B(t)^\top$, $E=B(t)^\top B(t)$, $X=LB(t)+B(t)R$. Then at every $t\in\mathbb R$
--   1. $u''(t)=4\sum_{a=0}^{s-1}\operatorname{tr}\big[D^{s-1-a}XE^aX^\top\big]\ge4\operatorname{tr}\big[D^{s-1}XX^\top\big]$ (5.11);
--   2. $u''(t)\le 8s\big(\operatorname{tr}[D^sL^2]+\operatorname{tr}[E^sR^2]\big)$ (5.12);
--   3. $|u'''(t)|\le 40s\max\{\|L\|_{op},\|R\|_{op}\}\,u''(t)$ (5.13).
--
--   At $t=0$ these are the displayed bounds with $D=BB^\top$, $E=B^\top B$, $X=LB+BR$; the source adds that they hold at every time with $B$ replaced by $B(t)$.
--
--   Differences from the source:
--   - encoding: the bounds at t = 0 plus 'the same bounds hold at every time t, with B replaced by B(t)' → one statement for every t with D, E, X formed from B(t); reason: at t = 0 e^0 = I gives the displayed case; the every-t clause is the source's last sentence
--   - encoding: e^{tL}, e^{tR}, u'', u''' → LowRankMEG.mexp (t • L), LowRankMEG.mexp (t • R), iteratedDeriv 2 and 3; reason: same objects for symmetric L, R
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Lemma 5.3, Eqs. (5.11)–(5.13), p.41

import Mathlib
import Definitions.Def_LowRankMEG_mexp
import Definitions.Def_LiqPremiaEq_opNorm

open Matrix Filter Topology
open scoped ContDiff Pointwise

namespace MatrixLeeSidford

/-- **Lemma 5.3 (Curvature along a matrix exponential curve)** (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), p.41). Let `B` be a
rectangular matrix, `L`, `R` real symmetric of compatible orders, `s ≥ 1` an integer,
`B(t) := e^{tL} B e^{tR}`, `u(t) := (1/s) tr[(B(t)B(t)ᵀ)^s]`, `D := BBᵀ`, `E := BᵀB`, `X := LB + BR`. Then
`u''(0) = 4 ∑_{a=0}^{s−1} tr[D^{s−1−a} X E^a Xᵀ] ≥ 4 tr[D^{s−1} X Xᵀ]` (5.11),
`u''(0) ≤ 8s (tr[D^s L²] + tr[E^s R²])` (5.12), `|u‴(0)| ≤ 40s max{‖L‖_op, ‖R‖_op} u''(0)` (5.13); the same
bounds hold at every time `t`, with `B` replaced by `B(t)`.

**Formalization Note** Stated at every `t` with `D, E, X` formed from `B(t)` (the case `t = 0` is
the displayed one, since `e^0 = I`). `e^{tL}` is `LowRankMEG.mexp (t • L)`. -/
theorem lemma_5_3 {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) (L : Matrix (Fin a) (Fin a) ℝ)
    (R : Matrix (Fin b) (Fin b) ℝ) (hL : L.IsHermitian) (hR : R.IsHermitian) (s : ℕ)
    (hs : 1 ≤ s) :
    let Bt : ℝ → Matrix (Fin a) (Fin b) ℝ := fun t => LowRankMEG.mexp (t • L) * B * LowRankMEG.mexp (t • R)
    let u : ℝ → ℝ := fun t => (1 / (s : ℝ)) * ((Bt t * (Bt t)ᵀ) ^ s).trace
    ∀ t : ℝ,
      let D := Bt t * (Bt t)ᵀ
      let E := (Bt t)ᵀ * Bt t
      let X := L * Bt t + Bt t * R
      iteratedDeriv 2 u t = 4 * ∑ c ∈ Finset.range s, (D ^ (s - 1 - c) * X * E ^ c * Xᵀ).trace ∧
      4 * (D ^ (s - 1) * X * Xᵀ).trace ≤ iteratedDeriv 2 u t ∧
      iteratedDeriv 2 u t ≤ 8 * (s : ℝ) * ((D ^ s * L ^ 2).trace + (E ^ s * R ^ 2).trace) ∧
      |iteratedDeriv 3 u t| ≤ 40 * (s : ℝ) * max (LiqPremiaEq.opNorm L) (LiqPremiaEq.opNorm R) * iteratedDeriv 2 u t := by sorry

end MatrixLeeSidford
