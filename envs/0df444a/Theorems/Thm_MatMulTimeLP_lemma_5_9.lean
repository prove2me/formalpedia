-- Prove2me | Theorems.Thm_MatMulTimeLP_lemma_5_9
-- name    : MatMulTimeLP.lemma_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:51:31.261277+00:00
-- url     : https://prove2.me/theorems/c12916f9-55ed-419f-bafd-a2e6a12bb51f
-- title:
--   Lemma 5.9 — cleanup lowers the potential by at least $C/100$
-- statement:
--   Let $n\ge 1$ and $\|a\|_1\le n$. Fix $z\in\mathbb R^n$ and a violated bucket $B_j(z)$, that is, $2^j|B_j(z)|>160n$. If $z'$ agrees with $z$ outside $B_j(z)$ and $z_i'=z_i/3$ on $B_j(z)$, then
--
--   $$D_\Psi(a,z')\le D_\Psi(a,z)-\frac{|B_j(z)|}{100}.$$
--
--   Consequently, a cleanup call performing $C$ coordinate shrinkages, counting multiplicity, decreases the potential by at least $C/100$.
--
--   So cleanup does not destroy progress; its potential decrease pays for each coordinate it shrinks, which bounds the total number of shrinkages in (11).
--
--   Differences from the source:
--   - generalization: $a$ the solution of the fix point equation, under the standing assumptions of p.25 → any vector with $\|a\|_1\le n$; no $H$, $h$; reason: the proof uses only $\|a\|_1\le n$; the page's case is an instance
-- source:
--   Jiang–Kyng–Zöcklein, Solving Linear Programs in Truly Matrix Multiplication Time, STOC 2027 submission (manuscript sha256 6539350a…81ffcc), Lemma 5.9, p.29

import Mathlib
import Definitions.Def_MatMulTimeLP_Chain

namespace MatMulTimeLP

/-- Jiang–Kyng–Zöcklein, *Solving Linear Programs in Truly Matrix Multiplication Time*, STOC 2027
submission (manuscript sha256 6539350a…81ffcc), Lemma 5.9, p.29: shrinking a violated bucket by `3` lowers
`D_Ψ(a, ·)` by at least `|B_j(z)|/100`, and a cleanup call performing `C` coordinate shrinkages lowers it by at
least `C/100`.

**Formalization Note** The standing assumption `‖a‖₁ ≤ n` (p.25) is the only property of `a` used, so `a` is any such
vector. -/
theorem lemma_5_9 {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : l1Norm a ≤ n) :
    (∀ (z : Fin n → ℝ) (j : ℕ), Violated z j →
      bregPsi a (shrink z j) ≤ bregPsi a z - ((bucket z j).card : ℝ) / 100) ∧
    ∀ z : Fin n → ℝ, bregPsi a (cleanup z).1 ≤ bregPsi a z - ((cleanup z).2 : ℝ) / 100 := by sorry

end MatMulTimeLP
