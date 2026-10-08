-- Prove2me | Theorems.Thm_OAI_InternalCatalan_determinantRat_prime_ne_zero
-- name    : OAI.InternalCatalan.determinantRat_prime_ne_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T19:00:32.417801+00:00
-- url     : https://prove2.me/theorems/990a48b8-bd24-43db-a87f-76e7f657a67c
-- title:
--   OpenAI Catalan, Proposition 4.1 — the rational determinant Δ_p(z) is nonzero for every large prime p
-- statement:
--   For a rational number $z$ and $N\ge1$ let $\Delta_N(z)\in\mathbb Q$ be the determinant of the paper's Eq. (7) with Catalan's constant $G$ replaced by $z$ in the moment evaluations (17) (`determinantRat z N`; for $z=G$ it is $\Delta_N$). Let $p_0(z)$ be the maximum of the denominator of $z$ and an explicit constant built from the three fixed determinants of Eq. (48) (`palindromicPrimeCutoff z`). Then for every prime $p>p_0(z)$,
--
--   $$\Delta_p(z)\ne0.$$
--
--   This supplies the infinite sequence of nonzero determinants along which the finite-place lower bound (Proposition 3.4) and the real-place upper bound (Proposition 7.1) are compared.
--
--   OpenAI, p. 19: “Proposition 4.1. Assume that $G\in\mathbb Q$. For every sufficiently large prime $p$, the determinant with scale parameter $N=p$ satisfies $v_p(\Delta_p)=-96p$. In particular, $\Delta_p\ne0$ for every sufficiently large prime $p$.”
--
--   **Formalization note.** The Lean statement is the “in particular” clause, for every rational $z$ in place of $G$, with an explicit threshold $p_0(z)$; the valuation identity $v_p(\Delta_p)=-96p$ is not stated. Source: OpenAI, *Catalan's constant is irrational*, OpenAI Math Release, September 24, 2026, [github.com/openai/math](https://github.com/openai/math) (Apache License 2.0).
-- source:
--   OpenAI, Catalan's constant is irrational, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf; Lean: lean/OAI/NumberTheory/Catalan, Apache License 2.0), p. 19, 24, Proposition 4.1

import Mathlib
import Definitions.Def_OAICatalanIrrationality

namespace OAI.InternalCatalan


theorem determinantRat_prime_ne_zero (z : ℚ) {p : ℕ} [Fact p.Prime]
    (hp : palindromicPrimeCutoff z < p) : determinantRat z p ≠ 0 := by
  sorry

end OAI.InternalCatalan
