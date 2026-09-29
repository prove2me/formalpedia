-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_level_indep_and_span_of_isPullback_of_faithfullyFlat
-- name    : GoodReductionJacobian.RelativeGroupLaw.level_indep_and_span_of_isPullback_of_faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/09b81ada-33e9-5af3-bf1f-98c0fb51759c
-- title:
--   Full level structure descends along faithfully flat base change
-- statement:
--   Let $S$ be a commutative ring and $S'$ a commutative $S$-algebra which is faithfully flat as an $S$-module, let $f : X \to \operatorname{Spec} S$ and $f' : A' \to \operatorname{Spec} S'$ be morphisms of schemes, and let $L$, $L'$ be relative group laws on $f$ and on $f'$, i.e. group structures on the sets $\{\varphi : T \to X \mid \varphi \circ f = t\}$ of sections over each base morphism $t$, natural in $t$. Let $c : A' \to X$ make the square with $f'$, $f$ and $\operatorname{Spec}(S \to S')$ cartesian, and assume $c$ is multiplicative: for every $t' : T \to \operatorname{Spec} S'$ and sections $x, y$ of $f'$ over $t'$, the composite of $L'.\mathrm{mul}\,t'\,x\,y$ with $c$ is the $L$-product of $x$ followed by $c$ and $y$ followed by $c$ over $t'$ followed by $\operatorname{Spec}(S \to S')$. Let $m, n$ be natural numbers, $P_0,\dots,P_{m-1}$ sections of $f$ over $\mathrm{id}_{\operatorname{Spec} S}$, $P'_0,\dots,P'_{m-1}$ sections of $f'$ over $\mathrm{id}_{\operatorname{Spec} S'}$, with $P'_i$ followed by $c$ equal to $\operatorname{Spec}(S \to S')$ followed by $P_i$. Assume that for every algebraically closed field $K$ and every ring homomorphism $S' \to K$, the combinations $\prod_i (P'_i)^{c_i}$, formed in the group of $K$-points of $f'$ over that homomorphism with exponents $c \in (\mathbb{Z}/n)^m$ read as naturals, are pairwise distinct, and that every $K$-point $Q$ of $f'$ with $nQ$ the identity is such a combination. The conclusion is the conjunction of the same two assertions for $L$ and the $P_i$: over every algebraically closed field $k$ and ring homomorphism $S \to k$, the map $c \mapsto \prod_i P_i^{c_i}$ from $(\mathbb{Z}/n)^m$ to $k$-points of $f$ is injective, and its image contains every $k$-point killed by $n$.
--
--   This is the descent statement saying that a full level-$n$ structure, given by generators $P_i$ together with the independence and spanning conditions on geometric fibres, may be checked after a faithfully flat base change $S \to S'$. It is used to produce the `P_indep` and `P_span` data of a polarised abelian scheme over $S$ from the corresponding data over $S'$, in [`AlgebraicGeometry.PolarisedAbelianScheme.exists_isPullback_of_descent_of_faithfullyFlat`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_isPullback_of_descent_of_faithfullyFlat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_level_indep_and_span_of_isPullback_of_faithfullyFlat.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.level_indep_and_span_of_isPullback_of_faithfullyFlat
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {X A' : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S')}
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (c : A' ⟶ X) (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (hcmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' f'),
      (L'.mul t' x y).1 ≫ c =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')))
          ⟨x.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, y.2]⟩).1)
    {m : ℕ} (n : ℕ) (P : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    (P' : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of S'))) f')
    (hP : ∀ i, (P' i).1 ≫ c = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ (P i).1)
    (hindep' : ∀ (K : Type u) [Field K] [IsAlgClosed K] (sK : S' →+* K) (c₁ c₂ : Fin m → Fin n),
      L'.finComb (Spec.map (CommRingCat.ofHom sK))
          (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sK)) (Category.comp_id _) (P' i)) (fun i => (c₁ i : ℕ)) =
        L'.finComb (Spec.map (CommRingCat.ofHom sK))
          (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sK)) (Category.comp_id _) (P' i)) (fun i => (c₂ i : ℕ)) →
        c₁ = c₂)
    (hspan' : ∀ (K : Type u) [Field K] [IsAlgClosed K] (sK : S' →+* K) (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sK)) f'),
      L'.nsmul (Spec.map (CommRingCat.ofHom sK)) n Q = L'.one (Spec.map (CommRingCat.ofHom sK)) →
        ∃ e : Fin m → Fin n,
          L'.finComb (Spec.map (CommRingCat.ofHom sK))
            (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sK)) (Category.comp_id _) (P' i)) (fun i => (e i : ℕ)) = Q) :
    (∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (c₁ c₂ : Fin m → Fin n),
      L.finComb (Spec.map (CommRingCat.ofHom sk))
          (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c₁ i : ℕ)) =
        L.finComb (Spec.map (CommRingCat.ofHom sk))
          (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c₂ i : ℕ)) →
        c₁ = c₂) ∧
    (∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f),
      L.nsmul (Spec.map (CommRingCat.ofHom sk)) n Q = L.one (Spec.map (CommRingCat.ofHom sk)) →
        ∃ e : Fin m → Fin n,
          L.finComb (Spec.map (CommRingCat.ofHom sk))
            (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (e i : ℕ)) = Q) := by sorry
