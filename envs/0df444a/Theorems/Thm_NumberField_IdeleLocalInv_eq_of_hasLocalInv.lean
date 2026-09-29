-- Prove2me | Theorems.Thm_NumberField_IdeleLocalInv_eq_of_hasLocalInv
-- name    : NumberField.IdeleLocalInv.eq_of_hasLocalInv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/24528273-1e77-5a1a-b9de-205af90cb1d0
-- title:
--   Uniqueness of the local invariant at a finite place
-- statement:
--   Let $E \subseteq K$ be number fields with $K/E$ Galois, let $D$ be an idèle Galois descent datum for $\mathcal{O}_K$ over $E \subseteq K$, that is, a monoid homomorphism $\mathrm{act}$ from $\mathrm{Gal}(K/E) = K \simeq_{\mathrm{alg}[E]} K$ to the ring automorphisms of the adèle ring $\mathbb{A}_K$, compatible with the embedding of $K$ and continuous in each element, and suppose the ambient multiplicative-distributive action of $\mathrm{Gal}(K/E)$ on the idèles $\mathbb{A}_K^\times$ agrees pointwise with the induced action `D.unitsAct` (hypothesis `hactI`). Let $x$ be a degree-$2$ group-cohomology class of the representation attached to this action of $\mathrm{Gal}(K/E)$ on $\mathbb{A}_K^\times$, let $v$ be a height-one prime of $\mathcal{O}_E$, and let $t_1, t_2 \in \mathbb{R}/\mathbb{Z}$, realised as `AddCircle (1 : ℚ)`. Assume both $t_1$ and $t_2$ satisfy `HasLocalInv E K D hactI x v`, i.e. for each there exist: a family of morphisms of representations $\mathrm{prG}$ realising, over each height-one prime $w$ of $\mathcal{O}_K$, the restriction to the decomposition subgroup $D_w$ of the idèle representation mapping to the $w$-component, given on elements by the coordinate map `finPart`; a prime $w$ of $\mathcal{O}_K$ contracting to $v$; a rational prime $q$ lying in $w$; a finite extension $L'$ of $\mathbb{Q}_q$ inside a fixed algebraic closure, with a faithful semiring action of $D_w$ fixing $\mathbb{Q}_q$ pointwise and compatible actions on units; an isomorphism $\Phi$ of $D_w$-rings from the completion $K_w$ to $L'$; a finite subextension $K_0$ which is the fixed field of $D_w$ in $L'$ in the sense of [`ExtCitation.LocalLevel.IsBase`](def/ExtCitation_LocalLevel_FundamentalClass.html#L13); a morphism $\theta$ from the units of $L'$ to the units of $K_w$ induced by $\Phi^{-1}$; a class $u'$ in $H^2(D_w, (L')^\times)$ that is a local fundamental class in the sense of `IsLocalFundamentalClass`; and an integer $n$ with the restriction of $x$ along $\mathrm{prG}(w)$ equal to $n \cdot \theta_* u'$ and $t$ the image of $n/\lvert D_w\rvert$ in $\mathbb{R}/\mathbb{Z}$. The conclusion is $t_1 = t_2$.
--
--   This is the well-definedness of the local invariant at a finite place of an idèle-valued degree-two cohomology class: the value in $\mathbb{Q}/\mathbb{Z}$ does not depend on the choice of place $w$ above $v$, of the $p$-adic realisation $\Phi$ of the completion, of the local fundamental class, or of the coordinate morphisms. It underlies the treatment of Brauer-type local invariants, being used for [`NumberField.LevelArith.eq_of_hasBrauerLocalInvAt`](thm.html#NumberField.LevelArith.eq_of_hasBrauerLocalInvAt), [`NumberField.LevelArith.hasBrauerLocalInvAt_add`](thm.html#NumberField.LevelArith.hasBrauerLocalInvAt_add) and [`NumberField.LevelArith.finsum_apply_eq_zero_of_isBrauerLocalInv`](thm.html#NumberField.LevelArith.finsum_apply_eq_zero_of_isBrauerLocalInv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_IdeleLocalInv_eq_of_hasLocalInv.lean

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
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open groupCohomology
open scoped NumberField.PlaceDecomp

theorem NumberField.IdeleLocalInv.eq_of_hasLocalInv
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (D : IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (x : groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) 2)
    (v : HeightOneSpectrum (𝓞 E)) (t₁ t₂ : AddCircle (1 : ℚ))
    (h₁ : NumberField.IdeleLocalInv.HasLocalInv E K D hactI x v t₁) (h₂ : NumberField.IdeleLocalInv.HasLocalInv E K D hactI x v t₂) :
    t₁ = t₂ := by sorry
