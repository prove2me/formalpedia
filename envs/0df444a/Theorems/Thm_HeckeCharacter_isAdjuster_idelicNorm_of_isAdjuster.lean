-- Prove2me | Theorems.Thm_HeckeCharacter_isAdjuster_idelicNorm_of_isAdjuster
-- name    : HeckeCharacter.isAdjuster_idelicNorm_of_isAdjuster
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/aabb077f-0688-5ad0-9ea1-be0b45f4ce15
-- title:
--   Adjusters descend along the idelic norm
-- statement:
--   Let $A$ and $B$ be number fields with $B$ an $A$-algebra, and let $\mathfrak m$ be an ideal of $\mathcal O_A$; let $v$ be a unit of the adele ring of $B$ and $\alpha \in B^\times$. Write $\mathfrak m\mathcal O_B$ for [`HeckeCharacter.modulusExt A B 𝔪`](def/LanglandsTunnell_ArtinCoreCTM.html#L25), the image ideal $\mathfrak m .\mathrm{map}(\mathcal O_A \to \mathcal O_B)$. The assertion is that if $\alpha$ is an adjuster for $v$ at level $\mathfrak m\mathcal O_B$ over $B$, meaning (i) for every height-one prime $w$ of $\mathcal O_B$ dividing $\mathfrak m\mathcal O_B$, the $w$-component of the finite part of the idele $v\cdot \iota(\alpha)^{-1}$ (with $\iota : B^\times \to (\mathbb A_B)^\times$ the principal-idele map) has valuation $1$ and its difference from $1$ has valuation at most $\exp(-n_w)$, where $n_w$ is the multiplicity of $w$ in the factorisation of $\mathfrak m\mathcal O_B$, and (ii) for every ring homomorphism $\tau : B \to \mathbb R$ the quantity $\mathrm{archRealProjTau}$ of $v\cdot\iota(\alpha)^{-1}$ at $\tau$ is strictly positive, then the idelic norm of $v$ along the base change `genuineBaseChange A B`, i.e. the image of $v$ under the unit map of the $\mathbb A_A$-algebra norm of $\mathbb A_B$, is adjusted by $N_{B/A}(\alpha) =$ `Units.map (Algebra.norm A) α` at level $\mathfrak m$ over $A$, in the same sense.
--
--   This is the norm compatibility of the congruence-and-positivity conditions that cut out a ray congruence subgroup modulo $\mathfrak m$: local norms respect the unit congruence filtration, and norms of elements positive at all real places are again positive at all real places of the base. It is used to transport adjusted principal ideles through the idelic norm, in the index computations for norm cosets of idele classes and in the construction of Hecke-character data for cyclic extensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeCharacter_isAdjuster_idelicNorm_of_isAdjuster.lean

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain

theorem HeckeCharacter.isAdjuster_idelicNorm_of_isAdjuster (A B : Type*) [Field A]
    [NumberField A] [Field B] [NumberField B] [Algebra A B] (𝔪 : Ideal (𝓞 A))
    {v : (AdeleRing (𝓞 B) B)ˣ} {α : Bˣ} :
    HeckeCharacter.IsAdjuster B (HeckeCharacter.modulusExt A B 𝔪) v α →
      HeckeCharacter.IsAdjuster A 𝔪
        ((M4aHerbrand.GenuineDescent.genuineBaseChange A B).idelicNorm v)
        (Units.map (Algebra.norm A) α) := by sorry
