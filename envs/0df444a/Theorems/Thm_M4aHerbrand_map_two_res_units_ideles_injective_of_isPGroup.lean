-- Prove2me | Theorems.Thm_M4aHerbrand_map_two_res_units_ideles_injective_of_isPGroup
-- name    : M4aHerbrand.map_two_res_units_ideles_injective_of_isPGroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/ff58c5cd-a393-5066-9a87-94ce06bdc43d
-- title:
--   Injectivity of H²(K^×)→ H²(I_K) for p-group layers
-- statement:
--   Let $E \subseteq K$ be number fields with $K/E$ Galois, write $\Gamma = K \simeq_{\mathrm{alg}[E]} K$ for the Galois group, and let $p$ be a prime such that $\Gamma$ is a $p$-group. Let $D$ be a descent datum for the Galois action on idèles, i.e. a monoid homomorphism $g \mapsto D.\mathrm{act}\,g$ from $\Gamma$ to the ring automorphisms of the adèle ring $\mathbb{A}_K$ (formed over $\mathcal{O}_K$) such that each $D.\mathrm{act}\,g$ is continuous and fixes the image of $K$ up to the action of $g$ on $K$. Assume given a multiplicative distributive action of $\Gamma$ on the unit group $\mathbb{A}_K^\times$ which coincides with the one induced by $D$ (the unit-group automorphism $D.\mathrm{unitsAct}\,g$ attached to $D.\mathrm{act}\,g$), a multiplicative distributive action of $\Gamma$ on $K^\times$, and a morphism $jK$ of the associated $\Gamma$-representations from $K^\times$ to $\mathbb{A}_K^\times$ whose underlying map is the principal-idèle embedding $a \mapsto \mathrm{algebraMap}\,a$ on units. (The action on $K^\times$ is constrained only by the requirement that $jK$ be $\Gamma$-equivariant together with this description of $jK$.) The conclusion is twofold: first, for every subgroup $S \le \Gamma$ the map induced by $jK$ on degree-two group cohomology of the restricted representations, $H^2(S, K^\times) \to H^2(S, \mathbb{A}_K^\times)$, is injective; second, for every subgroup $S \le \Gamma$ and every class $\beta \in H^2(\Gamma, K^\times)$, if the restriction to $S$ of $H^2(jK)(\beta)$ vanishes in $H^2(S, \mathbb{A}_K^\times)$ then the restriction of $\beta$ to $H^2(S, K^\times)$ vanishes.
--
--   This is the cohomological form of the Hasse principle for the layer $K/K^S$: the obstruction to injectivity of $H^2(S,K^\times) \to H^2(S,\mathbb{I}_K)$ in the long exact sequence attached to $1 \to K^\times \to \mathbb{I}_K \to C_K \to 1$ is $H^1(S, C_K)$, which vanishes for all subgroups of a $p$-group Galois group. It feeds the local–global comparison of degree-two classes used downstream in the Herbrand-quotient part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_map_two_res_units_ideles_injective_of_isPGroup.lean

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology NumberField M4aHerbrand

theorem M4aHerbrand.map_two_res_units_ideles_injective_of_isPGroup
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (p : ℕ) [Fact p.Prime] (hK : IsPGroup p (K ≃ₐ[E] K))
    (D : IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactIK : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (K ≃ₐ[E] K) Kˣ]
    (jK : Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ)
    (hjK : ∀ a : Kˣ, jK.hom (Additive.ofMul a) =
      Additive.ofMul (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a)) :
    (∀ S : Subgroup (K ≃ₐ[E] K),
      Function.Injective (groupCohomology.map
        (A := Rep.res S.subtype (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ))
        (B := Rep.res S.subtype (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ))
        (MonoidHom.id S) ((Rep.resFunctor S.subtype).map jK) 2).hom) ∧
    ∀ (S : Subgroup (K ≃ₐ[E] K)) (β : groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ) 2),
      (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ))) 2).hom
          ((groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) jK 2).hom β) = 0 →
      (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ))) 2).hom β = 0 := by sorry
