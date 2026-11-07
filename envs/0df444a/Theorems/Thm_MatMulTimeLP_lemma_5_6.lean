-- Prove2me | Theorems.Thm_MatMulTimeLP_lemma_5_6
-- name    : MatMulTimeLP.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:50:07.155879+00:00
-- url     : https://prove2.me/theorems/fca09074-5b2d-4c0f-8814-cd9a1422c25e
-- title:
--   Lemma 5.6 — $F$ is $1/2$-co-coercive and $2$-strongly monotone with respect to $D_\Psi$
-- statement:
--   Let $\|H\|_2\le 1$, $h\in\mathbb R^n$ and $F(z)=z-Hf(z)-h$. For every $z,y\in\mathbb R^n$,
--
--   $$\langle F(z)-F(y),z-y\rangle\ge 2\bigl(D_\Psi(z,y)+D_\Psi(y,z)\bigr)+\tfrac12\|F(z)-F(y)\|_2^2.$$
--
--   In particular, $F$ is $1/2$-co-coercive, and $2$-strongly monotone with respect to $D_\Psi$.
--
--   This explains the choice of $\psi$: its curvature matches the local contraction of $f$, so the relative strong monotonicity constant is absolute, whereas the Euclidean one is only $\Theta(1/n^2)$.
--
--   Differences from the source:
--   - generalization: the standing assumption $\|h\|_2\le n$ (p.25) → `h` arbitrary; reason: the proof does not use it; every $h$ with $\|h\|_2\le n$ is an instance
-- source:
--   Jiang–Kyng–Zöcklein, Solving Linear Programs in Truly Matrix Multiplication Time, STOC 2027 submission (manuscript sha256 6539350a…81ffcc), Lemma 5.6, p.26

import Mathlib
import Definitions.Def_MatMulTimeLP_FixPoint

open scoped Matrix.Norms.L2Operator

namespace MatMulTimeLP

open Matrix

/-- Jiang–Kyng–Zöcklein, *Solving Linear Programs in Truly Matrix Multiplication Time*, STOC 2027
submission (manuscript sha256 6539350a…81ffcc), Lemma 5.6, p.26:
`⟨F(z) - F(y), z - y⟩ ≥ 2(D_Ψ(z, y) + D_Ψ(y, z)) + ½‖F(z) - F(y)‖₂²`; in particular `F` is `1/2`-co-coercive and
`2`-strongly monotone with respect to `D_Ψ`.

**Formalization Note** Only `‖H‖₂ ≤ 1` is assumed; `h` is arbitrary, as the proof uses nothing else from the
section's standing assumptions. -/
theorem lemma_5_6 {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) (hH : ‖H‖ ≤ 1) :
    (∀ z y : Fin n → ℝ,
      2 * (bregPsi z y + bregPsi y z) +
          1 / 2 * ((fixF H h z - fixF H h y) ⬝ᵥ (fixF H h z - fixF H h y)) ≤
        (fixF H h z - fixF H h y) ⬝ᵥ (z - y)) ∧
    IsCoCoercive (fixF H h) (1 / 2) ∧ IsRelStronglyMonotone (fixF H h) bregPsi 2 := by sorry

end MatMulTimeLP
