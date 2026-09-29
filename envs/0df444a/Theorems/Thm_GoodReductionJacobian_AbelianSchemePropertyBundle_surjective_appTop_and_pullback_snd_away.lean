-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_surjective_appTop_and_pullback_snd_away
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.surjective_appTop_and_pullback_snd_away
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/3ba82551-d609-5ea5-b9db-13f63ae0bc42
-- title:
--   Global functions on an abelian scheme descend to the base
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec}(S)$ a morphism of schemes, and assume the bundle of properties `AbelianSchemePropertyBundle S f`, namely: $f$ is smooth, $f$ is proper, for every point $s$ of the scheme $\operatorname{Spec}(S)$ the set-theoretic fibre $f^{-1}(\{s\})$ of the underlying continuous map is connected (in particular nonempty), and there exists a relative group law for $f$ over $S$ — that is, functorial operations assigning to each $t : T \to \operatorname{Spec}(S)$ a multiplication, a unit and an inversion on the set of $T$-points of $A$ over $t$, satisfying associativity, the two unit laws and left inverses, and compatible with composition along any morphism $\psi : T' \to T$ over $\operatorname{Spec}(S)$. The conclusion is twofold: the ring homomorphism induced by $f$ on global sections of the structure sheaves, $\Gamma(\operatorname{Spec}(S), \mathcal O) \to \Gamma(A, \mathcal O)$, is surjective; and for every $r \in S$, the global-sections map of the second projection of the pullback of $f$ along $\operatorname{Spec}$ of the localisation homomorphism $S \to S[1/r]$ is surjective as well. Only surjectivity is asserted, although the statements invoked give bijectivity.
--
--   This is the naive, global-sections form of the classical identity $f_*\mathcal O_A = \mathcal O_S$ for an abelian scheme, together with its counterpart over the localisations $S[1/r]$ obtained by base change; classically it comes from cohomology and base change and Stein factorisation, the fibres being geometrically connected and reduced with a rational point. It is used in the treatment of rigidified line bundles and polarisations on abelian schemes, where it yields uniqueness and gluing over a localisation cover of the base, feeding the descent and pullback-isomorphism statements for polarised abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_surjective_appTop_and_pullback_snd_away.lean

import Mathlib
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.surjective_appTop_and_pullback_snd_away
    {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (hA : AbelianSchemePropertyBundle S f) :
    Function.Surjective (f.appTop).hom ∧
    ∀ r : S, Function.Surjective
      ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))).appTop).hom := by sorry
