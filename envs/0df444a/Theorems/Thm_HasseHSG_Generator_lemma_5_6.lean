-- Prove2me | Theorems.Thm_HasseHSG_Generator_lemma_5_6
-- name    : HasseHSG.Generator.lemma_5_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:35:43.724629+00:00
-- url     : https://prove2.me/theorems/ac9e70f2-2b06-4e51-8c30-761c7df508d9
-- title:
--   Lemma 5.6 (poles on q-orbits) — $F(q)(t)^{\sigma_q}=F(q)$; $g(qt)-g(t)$ never has exactly one pole on a $q$-orbit
-- statement:
--   Let $F$ be a field and $q$ transcendental over $F$. Let $g\in F(q)(t)$.
--
--   1. If $g(qt)=g(t)$, then $g\in F(q)$; that is, $F(q)(t)^{\sigma_q}=F(q)$.
--   2. For every $\alpha\ne0$, the rational function $g(qt)-g(t)$ cannot have exactly one pole on the $q$-orbit $\{q^m\alpha:m\in\mathbb Z\}$ of $\alpha$: it has either no pole there or at least two.
--
--   In the Lean statement, $\alpha$ ranges over an arbitrary field $E$ containing $F(q)$. A pole of $h\in F(q)(t)$ at $\beta\in E$ is a root of the reduced denominator of $h$. Item 2 then says
--   $$\neg\,\exists!\,\beta\in\{q^m\alpha:m\in\mathbb Z\}\ \text{with}\ \beta\ \text{a pole of}\ g(qt)-g(t).$$
--
--   The paper applies item 2 with $\alpha=1/a_i$ to show that $\sigma_q$-invariant polynomials in $x$ are constants (Lemma 5.8).
--
--   **Formalization Note.** $g(qt)$ is `sigmaT g`: the reduced numerator and denominator of $g$ are evaluated at $qt$.
--
--   Differences from the source:
--   - generalization: α ≠ 0 (the field containing α is not stated; the paper uses α = 1/a_i ∈ F) → α ≠ 0 in any field E with an F(q)-algebra structure; poles at points of E; reason: specializes to E = F(q) (and to an algebraic closure), which covers every use in the paper
--   - encoding: pole of h at β → β is a root of the reduced denominator RatFunc.denom h; reason: numerator and denominator are coprime
--   - encoding: q transcendental over F; F(q), F(q)(t) → RatFunc F with q = X; RatFunc (RatFunc F) with t = X; reason: Lean convention; F(q) is the rational function field in a transcendental
-- source:
--   Bal, Ghosh, Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary Characteristic Fields, STOC 2027 submission (held manuscript, sha256 1b7cccc3…), pp. 24–25, Lemma 5.6

import Mathlib
import Definitions.Def_HasseHSG_Generator_QDifference

namespace HasseHSG.Generator

/-- Lemma 5.6 (Poles on q-orbits, pp. 24–25). A pole of `h ∈ F(q)(t)` at a point `β` of a field
`E ⊇ F(q)` is a root of the (reduced) denominator of `h`; the `q`-orbit of `α` is
`{q^m α : m ∈ ℤ}`. -/
theorem lemma_5_6 {F : Type*} [Field F] (g : Fqt F) :
    (sigmaT g = g → ∃ c : Fq F, cK c = g) ∧
    ∀ (E : Type*) [Field E] [Algebra (Fq F) E] (α : E), α ≠ 0 →
      ¬ ∃! β : E, (∃ m : ℤ, β = (algebraMap (Fq F) E (qVar F)) ^ m * α) ∧
        Polynomial.aeval β (sigmaT g - g).denom = 0 := by sorry

end HasseHSG.Generator
