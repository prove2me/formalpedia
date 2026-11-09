-- Prove2me | Theorems.Thm_NadlerCLS_eq_C_10
-- name    : NadlerCLS.eq_C_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:55:34.8884+00:00
-- url     : https://prove2.me/theorems/78bcb3a1-d8a6-45d5-9824-15151ec44712
-- title:
--   Lemma C.8, output (N2) — the contraction step (C.10)
-- statement:
--   Let $p:X\to[0,1]$, $f:X\to X$ and $0<\delta<1$. If $x\ne y$, $f(x)\ne f(y)$, $p(f(x))<p(x)-\delta$ and $p(f(y))<p(y)-\delta$, then
--   $$ d_p(f(x),f(y))<d_p(x,y)-\delta\le(1-\delta/2)\,d_p(x,y). \tag{C.10} $$
--   With $k=1-\delta/2$ this contradicts an (N2) certificate, so one of $x,y$ is a (CO1) answer.
--
--   Differences from the source:
--   - generalization: $X=[0,1]^n$ → an arbitrary type; reason: the argument uses no structure of the cube
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), proof of Lemma C.8, output (N2), Eq. (C.10), p.39

import Mathlib
import Definitions.Def_NadlerCLS_dp

set_option autoImplicit false

namespace NadlerCLS

/-- **The contraction step (C.10) of Lemma C.8** (Xiong–Vlatakis-Gkaragkounis, *On the Complexity
of Finding Fixed Points for Set-Valued Contractions*, arXiv:2609.14101, held version of
2026-11-03, sha256 1fcc5a02…6dc485, proof of Lemma C.8, Output (N2), Eq. (C.10), p.39). Let
`p : α → [0, 1]`, `f : α → α` and `0 < δ < 1`. If `x ≠ y`, `f(x) ≠ f(y)`, `p(f(x)) < p(x) − δ` and
`p(f(y)) < p(y) − δ`, then
`d_p(f(x), f(y)) < d_p(x, y) − δ ≤ (1 − δ/2) d_p(x, y)`.

**Formalization Note** `α` is an arbitrary type (the paper's `X = [0, 1]ⁿ`). -/
theorem eq_C_10 {α : Type*} (p : α → ℝ) (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) (f : α → α) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (x y : α) (hxy : x ≠ y) (hfxy : f x ≠ f y)
    (hx : p (f x) < p x - δ) (hy : p (f y) < p y - δ) :
    dp p (f x) (f y) < dp p x y - δ ∧ dp p x y - δ ≤ (1 - δ / 2) * dp p x y := by sorry

end NadlerCLS
