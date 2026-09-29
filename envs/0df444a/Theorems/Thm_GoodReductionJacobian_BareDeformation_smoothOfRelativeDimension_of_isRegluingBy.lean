-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_smoothOfRelativeDimension_of_isRegluingBy
-- name    : GoodReductionJacobian.BareDeformation.smoothOfRelativeDimension_of_isRegluingBy
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/30fcf213-a673-5f10-9110-659232afa957
-- title:
--   Re-gluing preserves smoothness of relative dimension n
-- statement:
--   Fix a commutative ring $S$, a scheme $A_S$ with a morphism $f_S \colon A_S \to \operatorname{Spec} S$ and a relative group law $L_S$ on $f_S$, i.e. a functorial group structure on the sets of $T$-points of $f_S$ over $\operatorname{Spec} S$, and a commutative ring $B$ with an algebra structure making $S$ a $B$-algebra. Let $D_0$ and $D$ be bare deformations of $(f_S, L_S)$ to $B$: each consists of a scheme $A$, a morphism $f \colon A \to \operatorname{Spec} B$, a commutative relative group law $L$ on $f$, the property bundle asserting that $f$ is smooth and proper with connected fibres and carries a relative group law, a morphism $g \colon A_S \to A$ forming a pullback square with $f_S$, $f$ and $\operatorname{Spec}$ of $B \to S$, and the requirement that $g$ carry the multiplication of $L_S$ to that of $L$. Let $\mathcal U$ be an ordered affine cover of $D_0.A$: a finite linearly ordered index set $\iota$, together with affine opens $U_i$ whose supremum is the whole space. Let $\tau$ assign to each strictly monotone $s \colon \mathrm{Fin}\,2 \to \iota$ a self-isomorphism of the scheme $U_{s(0)} \cap U_{s(1)}$. Assume `D₀.IsRegluingBy 𝒰 τ D`, that is: each $\tau_s$ followed by the inclusion of the intersection into $D_0.A$ and then $D_0.f$ equals the inclusion followed by $D_0.f$; the restriction of $D_0.g$ to each intersection followed by $\tau_s$ equals that restriction; and there are morphisms $\iota_i \colon U_i \to D.A$, each an open immersion, with $\iota_i$ followed by $D.f$ equal to the inclusion $U_i \hookrightarrow D_0.A$ followed by $D_0.f$, jointly surjective on points, compatible with $D_0.g$ and $D.g$ on the preimages of the $U_i$, and satisfying on each overlap that the inclusion $U_{s(0)} \cap U_{s(1)} \hookrightarrow U_{s(0)}$ followed by $\iota_{s(0)}$ equals $\tau_s$ followed by the inclusion into $U_{s(1)}$ and then $\iota_{s(1)}$. Then, for a natural number $n$, if $D_0.f$ is smooth of relative dimension $n$, so is $D.f$.
--
--   The statement records that the property of being smooth of relative dimension $n$ is transported from a bare deformation to any deformation obtained from it by re-gluing the charts of an ordered affine cover along transition automorphisms, which is the classical fact that smoothness of a fixed relative dimension is local on the source. It is used in the study of bare deformations over dual numbers attached to fake elliptic curves, where the tangent-space computation requires re-glued deformations to retain the relative dimension of the original.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_smoothOfRelativeDimension_of_isRegluingBy.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.BareDeformation.smoothOfRelativeDimension_of_isRegluingBy
    {S : Type} [CommRing S] {Aₛ : Scheme.{0}} {fₛ : Aₛ ⟶ Spec (CommRingCat.of S)} {Lₛ : RelativeGroupLaw S fₛ}
    {B : Type} [CommRing B] [Algebra B S]
    (D₀ : BareDeformation fₛ Lₛ B) (𝒰 : D₀.A.OrderedAffineCover)
    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (D : BareDeformation fₛ Lₛ B) (hD : D₀.IsRegluingBy 𝒰 τ D)
    (n : ℕ) [SmoothOfRelativeDimension n D₀.f] :
    SmoothOfRelativeDimension n D.f := by sorry
