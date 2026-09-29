-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_baseChange_away_of_smooth_of_isProper
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.baseChange_away_of_smooth_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/e34a1d3a-fb94-5179-bb02-394db5b48d2e
-- title:
--   Base change to a basic open of a smooth proper family with connected fibres
-- statement:
--   Let $R$ be a commutative ring and let $f : A \to \operatorname{Spec} R$ be a morphism of schemes which is smooth (`Smooth f`) and proper (`IsProper f`) and whose topological fibres are connected: for every point $s$ of $\operatorname{Spec} R$ the set $f^{-1}(\{s\})$ is connected in the sense of `IsConnected` (nonempty and connected). Let $r \in R$ and write $g$ for the second projection of the pullback of $f$ along $\operatorname{Spec}$ of the localisation map $R \to R[1/r]$, so $g : A \times_{\operatorname{Spec} R} \operatorname{Spec} R[1/r] \to \operatorname{Spec} R[1/r]$. Assume given a term $L$ of `RelativeGroupLaw` for $g$ over $R[1/r]$, that is: for every scheme $T$ and every $t : T \to \operatorname{Spec} R[1/r]$ a multiplication, unit and inverse on the set of $t$-sections $\{\varphi : T \to A \times_{\operatorname{Spec} R} \operatorname{Spec} R[1/r] \mid \varphi \text{ followed by } g = t\}$, satisfying associativity, both unit laws and the left inverse law, with the multiplication natural under precomposition with morphisms $\psi : T' \to T$ over $\operatorname{Spec} R[1/r]$. Then $g$ satisfies `AbelianSchemePropertyBundle` over $R[1/r]$: it is smooth, proper, each of its topological fibres is connected, and it admits a relative group law.
--
--   This records that the four defining properties packaged in `AbelianSchemePropertyBundle` — smoothness, properness, connected fibres and the existence of a functorial relative group law — descend to the base change of a family over $\operatorname{Spec} R$ to a basic open $\operatorname{Spec} R[1/r]$, once a group law on that base change is supplied. It is used in the construction of a commutative relative group law on a smooth projective family over a Noetherian base, where the group law is first produced only after localising.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_baseChange_away_of_smooth_of_isProper.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.baseChange_away_of_smooth_of_isProper
    {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (hs : Smooth f) (hp : IsProper f) (hc : ∀ s : Spec (CommRingCat.of R), _root_.IsConnected (f.base ⁻¹' {s}))
    (r : R) (L : RelativeGroupLaw (Localization.Away r)
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))))) :
    AbelianSchemePropertyBundle (Localization.Away r)
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))) := by sorry
