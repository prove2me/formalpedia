-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_finite_and_projective_sections_of_closedImmersionBySections_type0
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.finite_and_projective_sections_of_closedImmersionBySections_type0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/06e34160-6152-5b70-b9dd-0176de58fea4
-- title:
--   Finite projective sections of an invertible module on an abelian scheme
-- statement:
--   Let $S$ be a commutative ring and let $f : A \to \operatorname{Spec} S$ be a morphism of schemes (all in the lowest universe). Assume given: a relative group law $L$ for $f$, that is, functorially in a scheme $T$ with a structure morphism $t : T \to \operatorname{Spec} S$ a group structure (multiplication, unit, inverse, with associativity, unit laws, left inverse and naturality in $T$) on the set of $T$-points $\{\varphi : T \to A \mid \varphi \circ f = t\}$; the bundle of properties `AbelianSchemePropertyBundle` for $f$, namely that $f$ is smooth, proper, that the fibre $f^{-1}(s)$ over every point $s$ of $\operatorname{Spec} S$ is connected, and that a relative group law exists; a module $\mathcal L$ on $A$ which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ on which the restriction of $\mathcal L$ is isomorphic to the unit module $\mathcal O_U$; and the hypothesis `ClosedImmersionBySections` for $\mathcal L$ and $f$, namely that for some $N$ there are sections $\sigma_0,\dots,\sigma_N \in \Gamma(\mathcal L,\top)$ together with a morphism $\pi_{\mathcal L} : A \to \mathbf P^N_S = \operatorname{Proj} S[X_0,\dots,X_N]$ over $\operatorname{Spec} S$ such that on every open $V$ contained in the preimage of the basic open set $D(X_i)$ multiplication by $\sigma_i|_V$ is a bijection $\Gamma(A,V) \to \Gamma(\mathcal L,V)$, the sections $\sigma_i,\sigma_j$ are related over $D(X_i)$ by the pullback of the ratio $X_j/X_i$, and $\pi_{\mathcal L}$ is a closed immersion. The conclusion is that $\Gamma(\mathcal L,\top)$, viewed as an $S$-module through the ring homomorphism $S \to \Gamma(A,\top)$ obtained from the inverse of the $\Gamma$–$\operatorname{Spec}$ adjunction isomorphism followed by $f$ on global sections, is both a finite and a projective $S$-module. No Noetherian hypothesis is imposed on $S$.
--
--   This is the statement that the global sections of a relatively very ample invertible module on an abelian scheme over an arbitrary (not necessarily Noetherian) affine base form a finitely generated projective module over the base, the projectivity half of the cohomology-and-base-change package for such bundles. It is used downstream in the construction of section bases compatible with base change for these modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_finite_and_projective_sections_of_closedImmersionBySections_type0.lean

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.finite_and_projective_sections_of_closedImmersionBySections_type0
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) (hva : Scheme.Modules.ClosedImmersionBySections 𝓛 f) :
    letI : Module S Γ(𝓛, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom
    Module.Finite S Γ(𝓛, ⊤) ∧ Module.Projective S Γ(𝓛, ⊤) := by sorry
