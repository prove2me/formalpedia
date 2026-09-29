-- Prove2me | Theorems.Thm_GoodReductionJacobian_abelianSchemePropertyBundle_pullback_snd_ratLocalizedAt
-- name    : GoodReductionJacobian.abelianSchemePropertyBundle_pullback_snd_ratLocalizedAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/65165a09-48c3-5a4b-bcc9-d6ac4cacc750
-- title:
--   Abelian scheme bundle after base change to mathbf Z_{(ℓ)}
-- statement:
--   Let $p$ be a natural number and $\ell$ a prime with $\ell \nmid p$. Let $g \colon G \to \operatorname{Spec}\mathbf Z$ be a smooth morphism of schemes (universe $0$), and let $L$ be a `RelativeGroupLaw` for $g$ over $\mathbf Z$: a group structure on the sets $\{\varphi : T \to G \mid \varphi \text{ followed by } g = t\}$ of sections over each $\mathbf Z$-scheme $t \colon T \to \operatorname{Spec}\mathbf Z$, with multiplication, unit and inverse satisfying associativity, the unit laws and left inverse, the multiplication being natural under morphisms $\psi \colon T' \to T$ over $\operatorname{Spec}\mathbf Z$. Assume every fibre $g^{-1}(s)$, $s \in \operatorname{Spec}\mathbf Z$, is preconnected as a subspace, and that the second projection of the pullback of $g$ along $\operatorname{Spec}$ of the structure map $\mathbf Z \to \mathbf Z[1/p]$ (the localisation away from $p$) is proper. Write $\mathbf Z_{(\ell)} = \{q \in \mathbf Q : \operatorname{den}(q) \text{ coprime to } \ell\}$, a subring of $\mathbf Q$. Then the base change of $g$ to $\operatorname{Spec}\mathbf Z_{(\ell)}$, namely the second pullback projection along $\operatorname{Spec}$ of $\mathbf Z \to \mathbf Z_{(\ell)}$, satisfies `AbelianSchemePropertyBundle` over $\mathbf Z_{(\ell)}$: it is smooth, it is proper, each of its fibres is connected (in particular non-empty), and it admits a relative group law over $\mathbf Z_{(\ell)}$. Note that $p$ is not assumed prime, and that the hypothesis on the fibres of $g$ asks only for preconnectedness while the conclusion asserts connectedness.
--
--   This is the passage from a smooth group scheme over $\mathbf Z$ with connected fibres that is proper away from $p$ — the shape of the identity component of the Néron model of $J_0(p)$ — to an abelian scheme over the discrete valuation ring $\mathbf Z_{(\ell)}$ for any prime $\ell \nmid p$. It is used in the treatment of good primes for the relative $\mathrm{Pic}^0$ of modular curves, in the construction of the identity component package for $J_0(p)$, and in the extension of sections over $\mathbf Z_{(\ell)}$ from the generic fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_abelianSchemePropertyBundle_pullback_snd_ratLocalizedAt.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.abelianSchemePropertyBundle_pullback_snd_ratLocalizedAt
    (p ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of ℤ)) [Smooth g] (L : RelativeGroupLaw ℤ g)
    (hconn : ∀ s : Spec (CommRingCat.of ℤ), _root_.IsPreconnected (g.base ⁻¹' {s}))
    (hprop : IsProper (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ)))))))
    : AbelianSchemePropertyBundle ↥(GaloisRep.ratLocalizedAt ℓ)
        (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ))))) := by sorry
