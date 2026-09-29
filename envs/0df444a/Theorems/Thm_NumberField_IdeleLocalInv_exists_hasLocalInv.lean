-- Prove2me | Theorems.Thm_NumberField_IdeleLocalInv_exists_hasLocalInv
-- name    : NumberField.IdeleLocalInv.exists_hasLocalInv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/9775d0bd-941a-59a4-b79b-41659b04703a
-- title:
--   Existence of a local invariant at each finite place of E
-- statement:
--   Let $E$ and $K$ be number fields with $K/E$ Galois, let $D$ be an `IdeleGaloisDescent` for $(\mathcal{O}_K, E, K)$, that is, a monoid homomorphism from $K \simeq_{\mathrm{alg}[E]} K$ to the ring automorphisms of the adèle ring $\mathbb{A}_K$ which is compatible with $\mathrm{algebraMap}$ from $K$ and continuous in each automorphism, and suppose the Galois group acts multiplicatively and distributively on $\mathbb{A}_K^{\times}$ in such a way that $g \cdot x = D.\mathrm{unitsAct}\ g\ x$ for all $g$ and $x$ (hypothesis `hactI`). Let $x$ be a degree-$2$ group cohomology class of the representation attached to this action on $\mathbb{A}_K^{\times}$, and let $v$ be a height-one prime of $\mathcal{O}_E$. The assertion is that some $t \in$ `AddCircle (1 : ℚ)`, i.e. $\mathbb{Q}/\mathbb{Z}$, satisfies `HasLocalInv E K D hactI x v t`: there exist a family $\mathrm{prG}$ of morphisms of representations, one for each height-one prime $w$ of $\mathcal{O}_K$, from the restriction of the idèle-units representation to the decomposition group $\mathrm{decomp}\,E\,K\,w$ to the units of the $w$-adic completion, realised on elements by `finPart w`; a prime $w$ of $\mathcal{O}_K$ contracting to $v$; a prime $q$ lying in $w$; a finite extension $L'$ of $\mathbb{Q}_q$ inside `PadicAlgCl q` carrying a faithful $\mathbb{Q}_q$-fixing semiring action of the decomposition group and a compatible distributive action on $(L')^{\times}$; a ring isomorphism $\Phi$ from the $w$-adic completion of $K$ onto $L'$ equivariant for these actions; a finite extension $K_0$ of $\mathbb{Q}_q$ which is a base for $L'$ and the decomposition group, i.e. $K_0 \le L'$ and an element of $L'$ lies in $K_0$ exactly when it is fixed by the whole group; a morphism $\theta$ from the units of $L'$ to the units of the completion induced on elements by $\Phi^{-1}$; a class $u'$ in $H^2$ of the units of $L'$ which is a local fundamental class in the sense of [`ExtCitation.LocalLevel.IsLocalFundamentalClass`](def/ExtCitation_LocalLevel_FundamentalClass.html#L60); and an integer $n$ such that the image of $x$ under the degree-$2$ map induced by the inclusion of the decomposition group together with $\mathrm{prG}\,w$ equals $n$ times the image of $u'$ under $\theta$, and $t$ is the class of $n/\#\mathrm{decomp}\,E\,K\,w$ modulo $1$.
--
--   This is the existence half of the theory of local invariants of idèle classes: every class in $H^2$ of the idèle units admits at least one value in $\mathbb{Q}/\mathbb{Z}$ realising the local invariant at a given finite place $v$ of $E$, computed by restricting to a decomposition group at a place $w$ above $v$, transporting to a finite level inside an algebraic closure of $\mathbb{Q}_q$ and comparing with the local fundamental class there. It is used, together with uniqueness and summation statements, by the Brauer-type local invariant results [`NumberField.LevelArith.exists_hasBrauerLocalInvAt`](thm.html#NumberField.LevelArith.exists_hasBrauerLocalInvAt), [`NumberField.LevelArith.finsum_apply_eq_zero_of_isBrauerLocalInv`](thm.html#NumberField.LevelArith.finsum_apply_eq_zero_of_isBrauerLocalInv) and [`NumberField.LevelArith.injective_of_isBrauerLocalInv`](thm.html#NumberField.LevelArith.injective_of_isBrauerLocalInv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_IdeleLocalInv_exists_hasLocalInv.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_IdeleLocalInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem NumberField.IdeleLocalInv.exists_hasLocalInv
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (D : IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (x : groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) 2)
    (v : HeightOneSpectrum (𝓞 E)) :
    ∃ t : AddCircle (1 : ℚ), NumberField.IdeleLocalInv.HasLocalInv E K D hactI x v t := by sorry
