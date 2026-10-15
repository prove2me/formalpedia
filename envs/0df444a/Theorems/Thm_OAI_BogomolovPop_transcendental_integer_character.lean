-- Prove2me | Theorems.Thm_OAI_BogomolovPop_transcendental_integer_character
-- name    : OAI.BogomolovPop.transcendental_integer_character
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T20:27:38.982171+00:00
-- url     : https://prove2.me/theorems/4c6d472b-6d5d-4993-b10f-14713a68f41f
-- title:
--   Transcendental elements are detected by homomorphisms $F^\times\to\mathbb{Z}$
-- statement:
--   Let $k$ be a field and let $F$ be a field extension of $k$ that is essentially of finite type over $k$; for a field this means that $F$ is finitely generated as a field over $k$. Let $u\in F^\times$ be transcendental over $k$. Then there is a group homomorphism $d$ from the multiplicative group $F^\times$ to the additive group $\mathbb Z$ that does not vanish at $u$:
--
--   $$
--   \exists\, d\in\operatorname{Hom}(F^\times,\mathbb Z)\qquad\text{with}\qquad d(u)\neq 0 .
--   $$
--
--   No assumption on $k$ (such as algebraic closedness) and no condition on the characteristic is needed.
--
--   Integer-valued characters of this kind behave like degree functions on $F^\times$. They turn multiplicative congruences in $F^\times$, for instance relations modulo $\ell^n$-th powers for every $n$, into equalities in $\mathbb Z_\ell$; this is how one shows that an $\ell$-adic scalar describing the action of a field endomorphism on Kummer classes must be a rational integer.
--
--   **Formalization Note** The codomain is `Multiplicative ℤ`, so the conclusion reads `∃ d : Fˣ →* Multiplicative ℤ, d u ≠ 1`; "essentially of finite type" is `Algebra.EssFiniteType k F`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/BogomolovPop/PowerCompletion.lean#L595-L642

import Mathlib
import Definitions.Def_BogomolovPopInjectivity
import Definitions.Def_OAI_Algebra_BogomolovPop_Foundations
import Definitions.Def_OAI_Algebra_BogomolovPop_Canonical
import Definitions.Def_OAI_Algebra_BogomolovPop_PowerCompletion

open OAI OAI.BogomolovPop
open scoped Topology

theorem OAI.BogomolovPop.transcendental_integer_character (k F : Type*) [Field k] [Field F]
    [Algebra k F] [Algebra.EssFiniteType k F] (u : Fˣ)
    (hu : Transcendental k (u : F)) :
    ∃ d : Fˣ →* Multiplicative ℤ, d u ≠ 1 := by sorry
