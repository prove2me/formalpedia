-- Prove2me | Theorems.Thm_HasseHSG_Generator_lemma_5_8
-- name    : HasseHSG.Generator.lemma_5_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:35:44.280789+00:00
-- url     : https://prove2.me/theorems/778614b3-cd64-418e-847c-17f88f87ca95
-- title:
--   Lemma 5.8 — $\sigma_q$-invariant elements of $F(q)(t)[x]$ lie in $F(q)$
-- statement:
--   Throughout, $F$ is an arbitrary field, $a_1,\dots,a_n\in F$ are distinct and nonzero, and $q$ is transcendental over $F$ (the standing assumptions of §5.3).
--
--   If $h\in B=F(q)(t)[x_1,\dots,x_n]$ satisfies $\sigma_q(h)=h$, then $h\in F(q)$; that is, $h$ is a constant polynomial whose value is free of $t$:
--
--   $$B^{\sigma_q}=F(q).$$
--
--   This is the polynomial case of the fixed-field theorem (Theorem 5.9). It needs both standing assumptions on the $a_i$: if $a_1=a_2$ then $x_1-x_2$ is invariant, and if $a_i=0$ then $x_i$ is invariant.
--
--   Differences from the source:
--   - encoding: q transcendental over F; F(q), F(q)(t) → RatFunc F with q = X; RatFunc (RatFunc F) with t = X; reason: Lean convention; F(q) is the rational function field in a transcendental
--   - encoding: h ∈ F(q) → ∃ c : F(q), C (cK c) = h; reason: membership in the embedded constant subfield, with no additional hypothesis
-- source:
--   Bal, Ghosh, Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary Characteristic Fields, STOC 2027 submission (held manuscript, sha256 1b7cccc3…), p. 26, Lemma 5.8

import Mathlib
import Definitions.Def_HasseHSG_Generator_QDifference

namespace HasseHSG.Generator

/-- Lemma 5.8 (p. 26): `σ_q`-invariant elements of `B = F(q)(t)[x₁, …, xₙ]` lie in `F(q)`. -/
theorem lemma_5_8 {F : Type*} [Field F] {n : ℕ} (a : Fin n → F)
    (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0)
    (h : BRing F n) (hh : sigmaB a h = h) :
    ∃ c : Fq F, MvPolynomial.C (cK c) = h := by sorry

end HasseHSG.Generator
