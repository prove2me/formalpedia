-- Prove2me | Theorems.Thm_IAFTRL_lemma_C_4
-- name    : IAFTRL.lemma_C_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:44:58.771639+00:00
-- url     : https://prove2.me/theorems/33859104-a7ba-41d9-a038-888988c4ef34
-- title:
--   Lemma C.4 — weighted least squares as a convex combination of interpolants
-- statement:
--   Let $x_1,\dots,x_m\in\mathbb R^r$, $z_1,\dots,z_m\in\mathbb R$ and weights $w_a\ge0$ be such that
--   $$
--   V=\sum_{a=1}^m w_a\,x_ax_a^\top\succ0 .
--   $$
--   For an $r$-element index set $I\subseteq\{1,\dots,m\}$ let $B_I$ be the $r\times r$ matrix with rows $x_a^\top$, $a\in I$, and, when $B_I$ is invertible, let $v_I=B_I^{-1}(z_a)_{a\in I}$ be the exact interpolant of the data indexed by $I$. Set
--   $$
--   \omega_I=\frac{\det(B_I)^2\prod_{a\in I}w_a}{\det V}.
--   $$
--   Then
--   $$
--   V^{-1}\sum_a w_a\,x_az_a=\sum_{I:\det B_I\ne0}\omega_I\,v_I,\qquad \omega_I\ge0,\qquad \sum_{I:\det B_I\ne0}\omega_I=1 .
--   $$
--
--   The weighted least-squares coefficient is thus a convex combination of exact interpolants; Lemma C.3 uses this to bound a least-squares residual by the interpolation constant $G_{\mathcal A}$.
--
--   **Formalization Note** Indices are `Fin m`; the rows of $B_I$ are taken in the increasing order of $I$, and none of $\det(B_I)^2$, $v_I$, $\omega_I$ depends on the row order.
--
--   Differences from the source:
--   - encoding: index set $I$ of actions, rows of $B_I$ unordered → $I$ a subset of `Fin m` of size $r$, rows of $B_I$ in increasing order of $I$; reason: $\det(B_I)^2$, $v_I$ and the residual do not depend on the row order
--   - generalization: $\omega_I\ge0$ for the index sets in the sum → $\omega_I\ge0$ for every $r$-element index set; reason: true for every $I$ ($\det^2\ge0$, $w\ge0$, $\det V>0$); specializes to the source
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Appendix C.2, Lemma C.4, p.62

import Mathlib

namespace IAFTRL

open Matrix

/-- **Lemma C.4 (Weighted least squares as a convex combination of interpolants).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299,
Lemma C.4, p.62: "If `V = Σ_a w_a x_a x_a^⊤ ≻ 0`, `w_a ≥ 0`, then
`V^{-1} Σ_a w_a x_a z_a = Σ_{I:det B_I≠0} ω_I v_I`, `ω_I = det(B_I)² Π_{a∈I} w_a / det V`, `ω_I ≥ 0`,
`Σ_I ω_I = 1`." In the proof: "Let `r = dim x_a`, let `X` have rows `x_a^⊤` … For `|I| = r`, let
`B_I = X_{I,:}`", and `v_I = B_I^{-1} z_I` ((C.44d)).

For points `x_a ∈ ℝ^r`, responses `z_a` and weights `w_a ≥ 0` (`a = 1, …, m`) with
`V = Σ_a w_a x_a x_a^⊤` positive definite: for each `r`-element index set `I`, `B_I` is the `r × r`
matrix with rows `x_a^⊤`, `a ∈ I`, `v_I = B_I^{-1}(z_a)_{a∈I}` the exact interpolant, and
`ω_I = det(B_I)² Π_{a∈I} w_a / det V`. Then the weighted least-squares coefficient
`V^{-1} Σ_a w_a z_a x_a` equals `Σ_{I : det B_I ≠ 0} ω_I v_I`, every `ω_I ≥ 0`, and the `ω_I` with
`det B_I ≠ 0` sum to `1`.

**Formalization Note.** Indices are `Fin m`; the rows of `B_I` follow the increasing order of `I`
(`I.orderEmbOfFin`); `det B_I²`, `v_I` and `ω_I` do not depend on the row order. `ω_I ≥ 0` is stated
for every `I`. -/
theorem lemma_C_4 {m r : ℕ} (x : Fin m → Fin r → ℝ) (z w : Fin m → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hV : (∑ a, w a • vecMulVec (x a) (x a)).PosDef) :
    let V : Matrix (Fin r) (Fin r) ℝ := ∑ a, w a • vecMulVec (x a) (x a)
    let B : {I : Finset (Fin m) // I.card = r} → Matrix (Fin r) (Fin r) ℝ :=
      fun I => Matrix.of fun i k => x (I.1.orderEmbOfFin I.2 i) k
    let vI : {I : Finset (Fin m) // I.card = r} → Fin r → ℝ :=
      fun I => (B I)⁻¹ *ᵥ fun i => z (I.1.orderEmbOfFin I.2 i)
    let ωI : {I : Finset (Fin m) // I.card = r} → ℝ :=
      fun I => (B I).det ^ 2 * (∏ a ∈ I.1, w a) / V.det
    V⁻¹ *ᵥ (∑ a, (w a * z a) • x a) =
        ∑ I ∈ Finset.univ.filter (fun I => (B I).det ≠ 0), ωI I • vI I ∧
      (∀ I, 0 ≤ ωI I) ∧
      ∑ I ∈ Finset.univ.filter (fun I => (B I).det ≠ 0), ωI I = 1 := by sorry

end IAFTRL
