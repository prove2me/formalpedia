-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_of_ramificationIdx_eq_one
-- name    : LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_of_ramificationIdx_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/4c65c1b2-4994-5932-87ee-6dea74894f79
-- title:
--   Level of ψ_w equals level of ψᵥ when e(w∣ v)=1
-- statement:
--   Let $E$ and $M$ be number fields with $M$ an $E$-algebra, let $v$ be a height-one prime of the ring of integers $\mathcal O_E$, and let $w$ be an element of `v.Extension (𝓞 M)`, i.e. a height-one prime $w$ of $\mathcal O_M$ whose contraction to $\mathcal O_E$ is $v$. Assume that the ramification index `ramificationIdx'` of $w$ over $v$ equals $1$ (no hypothesis on the residue degree is imposed). The conclusion compares two integers attached to the standard local additive characters: for a number field $K$ and a height-one prime $u$ of $\mathcal O_K$, `psiLocal K u` is the standard adelic additive character `stdAddChar K` (the character `psiK` of the adelic trace datum of $K$) composed with the additive homomorphism `adeleSingleAt K u` placing an element of the completion $K_u$ into the adele ring as a finite adele concentrated at $u$, and `addCharLevel ψ` is the supremum of the set of integers $n$ such that $\psi$ is trivial on every $x$ with $\mathrm{val}(x) \le \exp(n)$. The assertion is that `addCharLevel (psiLocal M w)` equals `addCharLevel (psiLocal E v)`.
--
--   This is the statement that the level (largest integer $n$ with triviality on the fractional ideal of valuation at most $\exp n$) of the standard additive character of a completion is unchanged on passing to a place with ramification index one in an extension of number fields. It is used in the comparison of local constants and root numbers in the cubic-induction step of the Langlands–Tunnell argument, where levels of additive characters at a place of the base and at a place above it must be matched.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_of_ramificationIdx_eq_one.lean

import Definitions.Def_DedekindDomain_IntegralClosure
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.StandardAddChar IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_of_ramificationIdx_eq_one
    (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))
    (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) :
    addCharLevel (psiLocal M w.1) = addCharLevel (psiLocal E v) := by sorry
