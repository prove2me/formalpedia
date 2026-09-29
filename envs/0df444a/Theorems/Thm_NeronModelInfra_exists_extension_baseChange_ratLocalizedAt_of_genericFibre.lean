-- Prove2me | Theorems.Thm_NeronModelInfra_exists_extension_baseChange_ratLocalizedAt_of_genericFibre
-- name    : NeronModelInfra.exists_extension_baseChange_ratLocalizedAt_of_genericFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/b4ddaa81-3264-5ae3-b759-d46508fab49a
-- title:
--   Extending generic-fibre endomorphisms over mathbf Z_{(ℓ)}
-- statement:
--   Let $p$ be a natural number and $\ell$ a prime (supplied as a `Fact`) with $\ell \nmid p$. Let $g : G \to \operatorname{Spec}\mathbf Z$ be a smooth morphism of schemes (over the base ring $\mathbf Z$), equipped with a `RelativeGroupLaw` $L$ for $g$, i.e. a functorial group structure on the sets $\{\varphi : T \to G \mid \varphi \circ\,\text{(structure map)} = t\}$ of sections over arbitrary $\mathbf Z$-schemes $t : T \to \operatorname{Spec}\mathbf Z$, with multiplication, unit and inverse satisfying associativity, the unit laws, left inversion, and naturality under base change along $\psi$ with $\psi \circ t' = t$ (in diagrammatic order). Assume each set-theoretic fibre $g^{-1}(s)$ of the underlying map of spaces is preconnected, and that the base change $G \times_{\mathbf Z} \mathbf Z[1/p] \to \operatorname{Spec}\mathbf Z[1/p]$, the second projection of the pullback of $g$ along $\operatorname{Spec}$ of $\mathbf Z \to \operatorname{Localization.Away}(p)$, is proper. Finally, let $v$ be an endomorphism of the generic fibre over $\mathbf Q$: a morphism $v_1 : G_{\mathbf Q} \to G_{\mathbf Q}$, where $G_{\mathbf Q} = G \times_{\mathbf Z} \operatorname{Spec}\mathbf Q$ is formed along $\operatorname{Spec}$ of $\mathbf Z \to \mathbf Q$, commuting with the projection to $\operatorname{Spec}\mathbf Q$. Write $\mathbf Z_{(\ell)} = \{q \in \mathbf Q : \gcd(\operatorname{den} q, \ell) = 1\}$, the subring [`GaloisRep.ratLocalizedAt`](def/GaloisRep_Flat.html#L8) $\ell$ of $\mathbf Q$, and $G_{(\ell)} = G \times_{\mathbf Z} \operatorname{Spec}\mathbf Z_{(\ell)}$. The assertion is that there exists $g_A : G_{(\ell)} \to G$ with $g_A$ followed by $g$ equal to the first projection followed by $g$, such that for every $j : G_{\mathbf Q} \to G_{(\ell)}$ compatible with the first projections to $G$ one has $j$ followed by $g_A$ equal to $v_1$ followed by the first projection $G_{\mathbf Q} \to G$.
--
--   This is the Néron mapping property at a prime $\ell \ne p$, in the proof-free shape required by the gluing statement that extension of a morphism from the generic fibre over a Dedekind base may be checked after localising at each maximal ideal; the compatibility with $j$ replaces the phrase "restricts to $v$ on the generic fibre", which is legitimate because $\operatorname{Spec}\mathbf Z_{(\ell)} \to \operatorname{Spec}\mathbf Z$ is a monomorphism so that such a $j$ is the canonical comparison map. It feeds the construction of Hecke endomorphisms of the identity component of the Néron model of $J_0(p)$ over $\mathbf Z$ from their generic-fibre counterparts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_extension_baseChange_ratLocalizedAt_of_genericFibre.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem NeronModelInfra.exists_extension_baseChange_ratLocalizedAt_of_genericFibre
    (p ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of ℤ)) [Smooth g] (L : RelativeGroupLaw ℤ g)
    (hconn : ∀ s : Spec (CommRingCat.of ℤ), _root_.IsPreconnected (g.base ⁻¹' {s}))
    (hprop : IsProper (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ)))))))
    (v : SchemeHomOver (pullback.snd g (specGenericFibreInclusion ℤ ℚ)) (pullback.snd g (specGenericFibreInclusion ℤ ℚ))) :
    ∃ gA : pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))) ⟶ G,
      gA ≫ g = pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))) ≫ g ∧
      ∀ j : pullback g (specGenericFibreInclusion ℤ ℚ) ⟶ pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))),
        j ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))) = pullback.fst g (specGenericFibreInclusion ℤ ℚ) →
        j ≫ gA = v.1 ≫ pullback.fst g (specGenericFibreInclusion ℤ ℚ) := by sorry
