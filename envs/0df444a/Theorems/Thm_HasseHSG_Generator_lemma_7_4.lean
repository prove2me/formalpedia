-- Prove2me | Theorems.Thm_HasseHSG_Generator_lemma_7_4
-- name    : HasseHSG.Generator.lemma_7_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:36:55.298444+00:00
-- url     : https://prove2.me/theorems/56e5fcc7-bb68-4dd7-b625-1db14bc86f0f
-- title:
--   Lemma 7.4 — $q$-partial closed $\iff$ stable under Hasse derivatives $\iff$ stable under translations
-- statement:
--   Throughout, $F$ is an arbitrary field, $a_1,\dots,a_n\in F$ are distinct and nonzero, and $q$ is transcendental over $F$ (the standing assumptions of §5.3).
--
--   For an $F(q)$-subspace $V\subseteq F(q)[x_1,\dots,x_n]$, the following are equivalent.
--
--   1. $V$ is $q$-partial closed: $\frac{d_q}{dx_i}V\subseteq F(q)(t)\otimes_{F(q)}V$ for all $i$ (Definition 7.1).
--   2. $V$ is stable under $\hat\partial^{(\gamma)}$ for all $\gamma\in\mathbb N^n$.
--   3. $V$ is stable under translations: $g(x+v)\in V$ for all $g\in V$ and $v\in F(q)^n$.
--
--   In particular, the $F(q)$-span of the Hasse derivative space of $f\in F[x]$ is $q$-partial closed. This is how Lemma 7.5 applies to it in Lemma 8.1.
--
--   **Formalization Note.** $\hat\partial^{(\gamma)}$ is `KakeyaHasse.hasse γ` over $F(q)$. The translate $g(x+v)$ is `aeval (fun i => X i + C (v i)) g`.
--
--   Differences from the source:
--   - encoding: F(q)(t) ⊗_{F(q)} V → the F(q)(t)-span of V inside B = F(q)(t)[x]; reason: the base change map is injective (p. 31), so the span is the tensor product
--   - encoding: q transcendental over F; F(q), F(q)(t) → RatFunc F with q = X; RatFunc (RatFunc F) with t = X; reason: Lean convention; F(q) is the rational function field in a transcendental
-- source:
--   Bal, Ghosh, Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary Characteristic Fields, STOC 2027 submission (held manuscript, sha256 1b7cccc3…), p. 32, Lemma 7.4 (proof pp. 32–34)

import Mathlib
import Definitions.Def_KakeyaPolynomialMethods
import Definitions.Def_HasseHSG_Generator_QDifference
import Definitions.Def_HasseHSG_Generator_QPartial

open MvPolynomial

namespace HasseHSG.Generator

/-- Lemma 7.4 (p. 32): for an `F(q)`-subspace `V ⊆ F(q)[x]`, `q`-partial closed ⇔ stable under
every Hasse derivative ⇔ stable under every translation by `v ∈ F(q)ⁿ`. -/
theorem lemma_7_4 {F : Type*} [Field F] {n : ℕ} (a : Fin n → F)
    (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0)
    (V : Submodule (Fq F) (MvPolynomial (Fin n) (Fq F))) :
    List.TFAE
      [IsQPartialClosed a V,
       ∀ γ : Fin n →₀ ℕ, ∀ g ∈ V, KakeyaHasse.hasse γ g ∈ V,
       ∀ g ∈ V, ∀ v : Fin n → Fq F, aeval (fun i => X i + C (v i)) g ∈ V] := by sorry

end HasseHSG.Generator
