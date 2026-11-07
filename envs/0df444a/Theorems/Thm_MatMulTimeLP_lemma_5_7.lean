-- Prove2me | Theorems.Thm_MatMulTimeLP_lemma_5_7
-- name    : MatMulTimeLP.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:51:34.568371+00:00
-- url     : https://prove2.me/theorems/7a2ba267-d931-4274-b244-961f775940a9
-- title:
--   Lemma 5.7 — the coordinate step is well-defined, with the required interval curvature
-- statement:
--   Let $z\in\mathbb R^n$, $r=Hf(z)+h-z$, $w_i=(2+|z_i|)^2+r_i^2$ and $\sigma_i=w_i^{-1}$. For every $i$, the point
--
--   $$\hat z_i=(\psi')^{-1}\Bigl(\psi'(z_i)+\frac{r_i}{8w_i}\Bigr)$$
--
--   is well-defined, and $\psi$ is $(2+|z_i|)^{-2}/2\ge\sigma_i/2$-strongly convex on the interval between $z_i$ and $\hat z_i$.
--
--   These are the hypotheses of Theorem 5.4 for the algorithm's step. They hold at every $z$, so the step never leaves the domain of $(\psi')^{-1}$.
--
--   Differences from the source:
--   - generalization: the standing assumptions $\|H\|_2\le 1$, $\|h\|_2\le n$ (p.25) → `H`, `h` arbitrary; reason: the proof uses only $w_i\ge 2(2+|z_i|)|r_i|$; the page's case is an instance
--   - encoding: "$\hat z_i$ is well-defined" → the dual point lies in $(-1/2,1/2)$, and $\psi'$ of `coordNew` equals it; reason: that is what well-definedness of the inverse means
-- source:
--   Jiang–Kyng–Zöcklein, Solving Linear Programs in Truly Matrix Multiplication Time, STOC 2027 submission (manuscript sha256 6539350a…81ffcc), Lemma 5.7, p.27

import Mathlib
import Definitions.Def_MatMulTimeLP_Chain

namespace MatMulTimeLP

/-- Jiang–Kyng–Zöcklein, *Solving Linear Programs in Truly Matrix Multiplication Time*, STOC 2027
submission (manuscript sha256 6539350a…81ffcc), Lemma 5.7, p.27: the point `ẑᵢ = (ψ')⁻¹(ψ'(zᵢ) + rᵢ/(8wᵢ))` is
well-defined, and `ψ` is `(2 + |zᵢ|)⁻²/2 ≥ σᵢ/2`-strongly convex on the interval between `zᵢ` and `ẑᵢ`, with
`σᵢ = wᵢ⁻¹`.

**Formalization Note** "Well-defined" is: the dual point lies in `(-1/2, 1/2)`, the range of `ψ'`, and `ψ'` sends
`coordNew` to it. -/
theorem lemma_5_7 {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (h z : Fin n → ℝ) (i : Fin n) :
    |dpsi (z i) + residual H h z i / (8 * weight H h z i)| < 1 / 2 ∧
    dpsi (coordNew H h z i) = dpsi (z i) + residual H h z i / (8 * weight H h z i) ∧
    StrongConvexOn (Set.uIcc (z i) (coordNew H h z i)) (((2 + |z i|) ^ 2)⁻¹ / 2) psi ∧
    (weight H h z i)⁻¹ / 2 ≤ ((2 + |z i|) ^ 2)⁻¹ / 2 := by sorry

end MatMulTimeLP
