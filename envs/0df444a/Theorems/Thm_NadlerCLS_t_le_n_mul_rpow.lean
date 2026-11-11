-- Prove2me | Theorems.Thm_NadlerCLS_t_le_n_mul_rpow
-- name    : NadlerCLS.t_le_n_mul_rpow
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T21:52:09.869392+00:00
-- url     : https://prove2.me/theorems/f9061745-2598-406d-a737-e3a9fe1147d6
-- title:
--   $t \le n\,t^{\beta}$ for $0 < t \le n$ (proof of Theorem C.3)
-- statement:
--   Let $n\ge1$ be a natural number, $\beta\in(0,1]$ and $0<t\le n$. Then
--   $$ t\le n\,t^{\beta}. $$
--   In the paper $t=\|x-y\|_1$ for points of $[0,1]^n$; the inequality converts a Hölder violation with constant $n\lambda$ into a Lipschitz violation with constant $\lambda$ (Theorem C.3, Lemma C.6 (C.7), Lemma C.8 output (N3)).
--
--   Differences from the source:
--   - generalization: the fixed rational exponent $\beta\in(0,1]$ → any real $\beta\in(0,1]$; reason: rational exponents are a special case
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), proof of Theorem C.3, p.37

import Mathlib

set_option autoImplicit false

namespace NadlerCLS

/-- **`t ≤ n t^β` on `(0, n]`** (Xiong–Vlatakis-Gkaragkounis, *On the Complexity of Finding Fixed
Points for Set-Valued Contractions*, arXiv:2609.14101, held version of 2026-11-03, sha256
1fcc5a02…6dc485, proof of Theorem C.3, p.37: "Since x, y ∈ [0, 1]n, one has 0 ≤ t ≤ n. For t > 0,
t1−β ≤ n1−β ≤ n, and hence t ≤ ntβ"). For a natural number `n ≥ 1`, a real `β ∈ (0, 1]` and
`0 < t ≤ n`, `t ≤ n · t^β`.

**Formalization Note** `t^β` is `Real.rpow`; `β` is real (the paper's fixed rational exponent is a
special case). -/
theorem t_le_n_mul_rpow (n : ℕ) (hn : 1 ≤ n) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (t : ℝ)
    (ht0 : 0 < t) (htn : t ≤ n) : t ≤ (n : ℝ) * t ^ β := by sorry

end NadlerCLS
