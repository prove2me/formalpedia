-- Prove2me | Theorems.Thm_HeckeCharacter_exists_isAdjuster
-- name    : HeckeCharacter.exists_isAdjuster
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/26251921-e21d-5b60-a440-f6fb80bc9bc3
-- title:
--   Existence of adjusters for idèles at level f
-- statement:
--   Let $K$ be a number field and let $\mathfrak f$ be a nonzero ideal of $\mathcal O_K$ (the hypothesis being $\mathfrak f \neq \bot$), and let $u$ be a unit of the adèle ring of $K$. The assertion is that there exists $\alpha \in K^\times$ such that the structure `IsAdjuster K 𝔣 u α` holds for the idèle $u' := u\cdot(\iota\alpha)^{-1}$, where $\iota$ is the map on unit groups induced by the structure morphism $K \to \mathbb A_K$. Unfolding the two fields of that structure: first, for every $v$ in the height-one spectrum of $\mathcal O_K$ with $v$ dividing $\mathfrak f$, the $v$-component of the finite part of $u'$ has valuation exactly $1$, and the valuation of that component minus $1$ is at most $\mathrm{exp}(-n_v)$ in $\mathbb Z_{\mathrm{m}0}$-valued notation, where $n_v$ is the multiplicity with which $v$ occurs in the factorisation of $\mathfrak f$ (the `Associates.mk` count); secondly, for every real embedding $\tau : K \to \mathbb R$, the predicate `archSign K τ u'` holds, i.e. the real number `archRealProjTau K τ u'` attached to $u'$ at $\tau$ is strictly positive. Thus $u$ becomes, after multiplication by a global element, multiplicatively congruent to $1$ modulo $\mathfrak f$ and positive at every real place.
--
--   This is the weak-approximation step which shows that every idèle class of a number field has a representative adjusted at level $\mathfrak f\cdot\infty$, the statement making the content map from adjusted idèles to ray classes defined on the whole idèle class group. It is used in the construction of the idèle-class/ray-class dictionary and of the idelic reciprocity map, in particular by [`LanglandsTunnell.P2.Artin.exists_mulEquiv_quotient_normRaySubgroup_apply_eq_contents_of_anchors`](thm.html#LanglandsTunnell.P2.Artin.exists_mulEquiv_quotient_normRaySubgroup_apply_eq_contents_of_anchors), by [`LanglandsTunnell.P2.Artin.eq_finprod_artinFrob_pow_placeOrd_of_isAdjuster_one_of_dvd`](thm.html#LanglandsTunnell.P2.Artin.eq_finprod_artinFrob_pow_placeOrd_of_isAdjuster_one_of_dvd) and by `M4aHerbrand.restrictNormalHom_idelicArtinMax_eq`'s analogue [`M4aHerbrand.restrictNormalHom_idelicArtinMap_eq`](thm.html#M4aHerbrand.restrictNormalHom_idelicArtinMap_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeCharacter_exists_isAdjuster.lean

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors

theorem HeckeCharacter.exists_isAdjuster
    (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥) (u : (AdeleRing (𝓞 K) K)ˣ) :
    ∃ α : Kˣ, IsAdjuster K 𝔣 u α := by sorry
