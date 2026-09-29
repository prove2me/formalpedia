-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_isAdmissibleTwist_mul_comp_idelicNorm_of_isFiniteOrderHeckeChar
-- name    : LanglandsTunnell.Converse.isAdmissibleTwist_mul_comp_idelicNorm_of_isFiniteOrderHeckeChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/93425766-385b-5267-af22-b05e08d92190
-- title:
--   Twisting an admissible character by the idelic norm
-- statement:
--   Let $E$ and $M$ be number fields with $M$ an $E$-algebra, and let $\xi \colon (\mathbf{A}_M)^\times \to \mathbb{C}^\times$ and $\mu \colon (\mathbf{A}_E)^\times \to \mathbb{C}^\times$ be group homomorphisms on the idele groups of the adele rings of $M$ and $E$ respectively. Assume $\xi$ satisfies `IsFiniteOrderHeckeChar`, i.e. $\xi$ is trivial on the principal ideles (for every $u \in M^\times$, $\xi$ of the image of $u$ under $M^\times \to (\mathbf{A}_M)^\times$ equals $1$), $\xi$ is continuous, and $\xi$ is of finite order in the group of such homomorphisms. Assume $\mu$ satisfies `IsAdmissibleTwist`, i.e. $\mu$ is trivial on the principal ideles of $E$, continuous, and unitary ($\lVert \mu(x) \rVert = 1$ for all $x$). Then the pointwise product of $\xi$ with the composite of $\mu$ after the idelic norm $(\mathbf{A}_M)^\times \to (\mathbf{A}_E)^\times$ attached to the base change `genuineBaseChange E M` — the map induced on units by the algebra norm of $\mathbf{A}_M$ over $\mathbf{A}_E$ — again satisfies `IsAdmissibleTwist` over $M$: it is trivial on $M^\times$, continuous, and unitary.
--
--   This is the standard fact that a finite-order Hecke character of $M$ times the norm pull-back of a continuous unitary idele class character of $E$ is again such a character of $M$. It is used to produce admissible twists over the larger field, feeding the statements on self-inverse admissible twists with prescribed local behaviour at uniformiser ideles and at unramified or bounded-discriminant places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_isAdmissibleTwist_mul_comp_idelicNorm_of_isFiniteOrderHeckeChar.lean

import Mathlib
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField HeckeCharacter LanglandsTunnell.Converse M4aHerbrand.GenuineDescent

theorem LanglandsTunnell.Converse.isAdmissibleTwist_mul_comp_idelicNorm_of_isFiniteOrderHeckeChar
    (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (hξ : IsFiniteOrderHeckeChar M ξ)
    (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist E μ) :
    IsAdmissibleTwist M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) := by sorry
