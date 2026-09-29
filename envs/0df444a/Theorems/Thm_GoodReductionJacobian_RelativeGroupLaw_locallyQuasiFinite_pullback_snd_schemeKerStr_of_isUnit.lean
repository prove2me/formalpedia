-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_pullback_snd_schemeKerStr_of_isUnit
-- name    : GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_pullback_snd_schemeKerStr_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/527036fe-b3d5-5a74-b03c-156ebee9f886
-- title:
--   Kernel of [n] is locally quasi-finite over a field point where n is invertible
-- statement:
--   Let $R$ be a commutative ring and $K$ a field, and let $\iota \colon \operatorname{Spec} K \to \operatorname{Spec} R$ be any morphism of schemes. Let $f \colon A \to \operatorname{Spec} R$ be a morphism of schemes that is locally of finite type, and let $G$ be a relative group law on $f$ in the sense of `RelativeGroupLaw`: for every scheme $T$ and every $t \colon T \to \operatorname{Spec} R$ a multiplication, unit and inversion on the set $\{\varphi \colon T \to A \mid \varphi$ followed by $f$ equals $t\}$ of $T$-points of $A$ over $t$, satisfying associativity, the two unit laws, the left inverse law, and naturality of the multiplication under precomposition with a morphism $\psi \colon T' \to T$ over $\operatorname{Spec} R$. Assume moreover (hypothesis `hcomm`) that this multiplication is commutative for every $T$, every $t$ and every pair of points. Let $n$ be a natural number whose image in $K$ is a unit. Then the second projection of the pullback of `G.schemeKerStr n` along $\iota$ is locally quasi-finite, where `G.schemeKerStr n` is the second projection of the fibre product of the multiplication-by-$n$ endomorphism `G.schemeNsmul n` of $A$ (the underlying morphism of the $n$-fold $G$-sum of the tautological identity point of $A$) with the unit section $\operatorname{Spec} R \to A$ of $G$ at the identity of $\operatorname{Spec} R$; that is, $A[n] \times_{\operatorname{Spec} R} \operatorname{Spec} K \to \operatorname{Spec} K$ is locally quasi-finite.
--
--   This is the standard statement that the $n$-torsion subscheme of a commutative group scheme is quasi-finite over the base wherever $n$ is invertible, here in the form of a fibrewise assertion at an arbitrary field-valued point of $\operatorname{Spec} R$. It feeds the finiteness and étaleness statements for kernels of $[n]$ used in the treatment of abelian schemes and of fake elliptic curves in the Cherednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_pullback_snd_schemeKerStr_of_isUnit.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_pullback_snd_schemeKerStr_of_isUnit
    {R : Type u} [CommRing R] {K : Type u} [Field K]
    (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} [LocallyOfFiniteType f]
    (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : K)) :
    LocallyQuasiFinite (pullback.snd (G.schemeKerStr n) ι) := by sorry
