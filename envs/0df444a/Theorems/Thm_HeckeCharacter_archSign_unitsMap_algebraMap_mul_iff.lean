-- Prove2me | Theorems.Thm_HeckeCharacter_archSign_unitsMap_algebraMap_mul_iff
-- name    : HeckeCharacter.archSign_unitsMap_algebraMap_mul_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/db7bdfa6-6b21-582c-ac85-31805c54d1d6
-- title:
--   Sign at a real place of a principal translate of an idèle
-- statement:
--   Let $K$ be a number field, let $\tau : K \to \mathbb{R}$ be a ring homomorphism, let $\alpha \in K^\times$, and let $u$ be a unit of the adèle ring $\mathbb{A}_K$ of $K$ (formed over $\mathcal{O}_K$). Write $\mathrm{archSign}\,K\,\tau\,v$ for the assertion that the real number $\mathrm{archRealProjTau}\,K\,\tau\,v$ is positive, that is, that the component of the idèle $v$ at the infinite place $\mathrm{placeOf}\,K\,\tau$ determined by $\tau$, transported to $\mathbb{R}$ by the isomorphism of the completion at that place with $\mathbb{R}$ coming from its being real, is positive. The theorem asserts the equivalence
--   $$\mathrm{archSign}\,K\,\tau\bigl(\iota(\alpha)\cdot u\bigr) \iff \bigl(0 < \tau(\alpha) \iff \mathrm{archSign}\,K\,\tau\,u\bigr),$$
--   where $\iota$ denotes the map on unit groups induced by the structure morphism $K \to \mathbb{A}_K$. In words: the principal translate $\alpha u$ is positive at the real place attached to $\tau$ exactly when $u$ is positive there if and only if $\tau(\alpha)$ is positive.
--
--   This is the elementary sign rule at a real place for multiplying an idèle by a principal idèle, in the form needed to prescribe archimedean signs by a global element. It is used in the construction of adjusting elements ([`HeckeCharacter.exists_isAdjuster`](thm.html#HeckeCharacter.exists_isAdjuster)), in the identification of the quotient by a norm ray subgroup with prescribed contents in the Artin-map analysis, and in the vanishing of idelic Artin-map products on totally positive elements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeCharacter_archSign_unitsMap_algebraMap_mul_iff.lean

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors

theorem HeckeCharacter.archSign_unitsMap_algebraMap_mul_iff
    (K : Type*) [Field K] [NumberField K] (τ : K →+* ℝ) (α : Kˣ) (u : (AdeleRing (𝓞 K) K)ˣ) :
    archSign K τ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) α * u) ↔
      (0 < τ α ↔ archSign K τ u) := by sorry
