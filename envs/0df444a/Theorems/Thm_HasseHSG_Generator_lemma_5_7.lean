-- Prove2me | Theorems.Thm_HasseHSG_Generator_lemma_5_7
-- name    : HasseHSG.Generator.lemma_5_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:35:51.384666+00:00
-- url     : https://prove2.me/theorems/c66c3266-74f9-4a36-b7ad-f2a6640acccf
-- title:
--   Lemma 5.7 — $\sigma_q$ commutes with every Hasse derivative on $F(q)(t)[x]$
-- statement:
--   Throughout, $F$ is an arbitrary field, $a_1,\dots,a_n\in F$ are distinct and nonzero, and $q$ is transcendental over $F$ (the standing assumptions of §5.3). Let $B=F(q)(t)[x_1,\dots,x_n]$ and $\sigma_q(f)(t,x)=f(qt,x_1+c_1(t),\dots,x_n+c_n(t))$.
--
--   For every $f\in B$ and every $\gamma\in\mathbb N^n$,
--
--   $$\hat\partial^{(\gamma)}\sigma_q(f)=\sigma_q\bigl(\hat\partial^{(\gamma)}f\bigr),$$
--
--   where $\hat\partial^{(\gamma)}$ is the Hasse derivative in $x$ with coefficients in $F(q)(t)$. Lemma 5.8 uses this to show that every Hasse derivative of a $\sigma_q$-invariant polynomial is again $\sigma_q$-invariant.
--
--   **Formalization Note.** $\hat\partial^{(\gamma)}$ is `KakeyaHasse.hasse γ` over the coefficient ring $F(q)(t)$.
--
--   Differences from the source:
--   - encoding: Hasse derivative as the coefficient of y^γ in f(x + y) → KakeyaHasse.hasse γ (coefficient of x^β is binom(β+γ, γ)·f_{β+γ}); reason: the same polynomial
--   - encoding: q transcendental over F; F(q), F(q)(t) → RatFunc F with q = X; RatFunc (RatFunc F) with t = X; reason: Lean convention; F(q) is the rational function field in a transcendental
-- source:
--   Bal, Ghosh, Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary Characteristic Fields, STOC 2027 submission (held manuscript, sha256 1b7cccc3…), p. 25, Lemma 5.7

import Mathlib
import Definitions.Def_KakeyaPolynomialMethods
import Definitions.Def_HasseHSG_Generator_QDifference

namespace HasseHSG.Generator

/-- Lemma 5.7 (p. 25): `σ_q` commutes with every Hasse derivative on `B = F(q)(t)[x]`. -/
theorem lemma_5_7 {F : Type*} [Field F] {n : ℕ} (a : Fin n → F)
    (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0)
    (f : BRing F n) (γ : Fin n →₀ ℕ) :
    KakeyaHasse.hasse γ (sigmaB a f) = sigmaB a (KakeyaHasse.hasse γ f) := by sorry

end HasseHSG.Generator
