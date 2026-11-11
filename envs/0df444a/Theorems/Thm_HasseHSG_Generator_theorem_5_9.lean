-- Prove2me | Theorems.Thm_HasseHSG_Generator_theorem_5_9
-- name    : HasseHSG.Generator.theorem_5_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:35:51.018025+00:00
-- url     : https://prove2.me/theorems/9ba2a679-1808-4dfe-908c-32c88bf75fcc
-- title:
--   Theorem 5.9 (fixed subfield under $\sigma_q$) — $L^{\sigma_q}=F(q)$
-- statement:
--   Throughout, $F$ is an arbitrary field, $a_1,\dots,a_n\in F$ are distinct and nonzero, and $q$ is transcendental over $F$ (the standing assumptions of §5.3). Let $L=\operatorname{Frac}(F(q)(t)[x_1,\dots,x_n])$ and extend $\sigma_q$ to $L$ by $\sigma_q(u/v)=\sigma_q(u)/\sigma_q(v)$.
--
--   If $h\in L$ satisfies $\sigma_q(h)=h$, then $h\in F(q)$. In other words,
--
--   $$L^{\sigma_q}=F(q).$$
--
--   Through the Casoratian criterion (Lemma 6.4), this identifies linear independence over the fixed field with linear independence over $F(q)$, which is what makes the $D_{q,d}$-Wronskian detect $F(q)$-linear independence (Theorem 6.2).
--
--   **Formalization Note.** $F(q)\subseteq L$ is the composite inclusion `embFqL`.
--
--   Differences from the source:
--   - encoding: q transcendental over F; F(q), F(q)(t) → RatFunc F with q = X; RatFunc (RatFunc F) with t = X; reason: Lean convention; F(q) is the rational function field in a transcendental
--   - encoding: h ∈ F(q) → ∃ c : F(q), embFqL c = h; reason: membership in the embedded constant subfield, with no additional hypothesis
-- source:
--   Bal, Ghosh, Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary Characteristic Fields, STOC 2027 submission (held manuscript, sha256 1b7cccc3…), p. 27, Theorem 5.9

import Mathlib
import Definitions.Def_HasseHSG_Generator_QDifference

namespace HasseHSG.Generator

/-- Theorem 5.9 (Fixed subfield under σ_q, p. 27): `L^{σ_q} = F(q)`. -/
theorem theorem_5_9 {F : Type*} [Field F] {n : ℕ} (a : Fin n → F)
    (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0)
    (h : LField F n) (hh : sigmaL a h = h) :
    ∃ c : Fq F, embFqL c = h := by sorry

end HasseHSG.Generator
