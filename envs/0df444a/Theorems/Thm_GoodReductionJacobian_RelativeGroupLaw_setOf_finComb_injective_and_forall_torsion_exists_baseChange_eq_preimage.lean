-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_setOf_finComb_injective_and_forall_torsion_exists_baseChange_eq_preimage
-- name    : GoodReductionJacobian.RelativeGroupLaw.setOf_finComb_injective_and_forall_torsion_exists_baseChange_eq_preimage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/ac28f807-8aa1-5633-84c2-756506f65470
-- title:
--   Base-change compatibility of the level-n basis locus
-- statement:
--   Let $S$ be a commutative ring, $f : A \to \operatorname{Spec} S$ a morphism of schemes, and $L$ a `RelativeGroupLaw` for $f$, that is, a group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $A$-valued points over each $t : T \to \operatorname{Spec} S$, natural in $T$; assume $L$ is commutative, that $f$ carries an `AbelianSchemePropertyBundle` (smooth, proper, with connected fibres and admitting a relative group law), and that every fibre $f^{-1}(s)$ has topological Krull dimension $g$. Let $n$ be a natural number whose image in $S$ is a unit, and $P_1,\dots,P_{2g}$ sections of $f$ over the identity of $\operatorname{Spec} S$. Let $\varphi : S \to S'$ be a ring homomorphism, $f' : A' \to \operatorname{Spec} S'$ with a relative group law $L'$, and $g_A : A' \to A$ making $(g_A, f', f, \operatorname{Spec} \varphi)$ a pullback square, compatible with the two group laws in the sense that composing a product of $T$-points for $L'$ with $g_A$ is the $L$-product of the composites; let $P'_i$ be sections of $f'$ with $(P'_i) \circ g_A = g_A$-compatible images of $P_i$, i.e. $(P'_i).1 \gg g_A = \operatorname{Spec}\varphi \gg (P_i).1$. The conclusion is an equality of subsets of $\operatorname{Spec} S'$: the set of points $s$ such that for every algebraically closed field $k$ and every ring homomorphism $sk : S' \to k$ with kernel the prime of $s$, (i) the map sending $c \in (\mathrm{Fin}\,n)^{2g}$ to the `finComb` combination $\prod_i (P'_i)^{c_i}$ of the base-changed sections over $\operatorname{Spec} sk$ is injective, and (ii) every point $Q$ of $A'$ over $\operatorname{Spec} sk$ with $nQ$ equal to the identity is such a combination, coincides with the preimage under the map on points induced by $\operatorname{Spec}\varphi$ of the set defined by the same two conditions for $f$, $L$ and the $P_i$.
--
--   This is the statement that the locus in the base where the chosen $n$-torsion sections give a level-$n$ basis at geometric points is stable under, and cut out by, base change, the $S'$-locus being exactly the preimage of the $S$-locus. It is used in the construction of immersions representing framed polarised abelian schemes over Noetherian bases, in [`AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isImmersion_proj_represents_embedded_of_isNoetherianRing`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isImmersion_proj_represents_embedded_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_setOf_finComb_injective_and_forall_torsion_exists_baseChange_eq_preimage.lean

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

attribute [local instance] MvPolynomial.gradedAlgebra

theorem GoodReductionJacobian.RelativeGroupLaw.setOf_finComb_injective_and_forall_torsion_exists_baseChange_eq_preimage
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of S)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (n : ℕ) (hn : IsUnit ((n : ℕ) : S))
    (P : Fin (2 * g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    {S' : Type} [CommRing S'] (φ : S →+* S')
    {A' : Scheme} {f' : A' ⟶ Spec (CommRingCat.of S')} (L' : RelativeGroupLaw S' f')
    (gA : A' ⟶ A) (hgA : IsPullback gA f' f (Spec.map (CommRingCat.ofHom φ)))
    (hgA_mul : ∀ {T : Scheme} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' f'),
      (L'.mul t' x y).1 ≫ gA =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ gA, by rw [Category.assoc, hgA.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gA, by rw [Category.assoc, hgA.w, ← Category.assoc, y.2]⟩).1)
    (P' : Fin (2 * g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of S'))) f')
    (hP' : ∀ i, (P' i).1 ≫ gA = Spec.map (CommRingCat.ofHom φ) ≫ (P i).1) :
    {s : ↥(Spec (CommRingCat.of S')) | ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k),
      RingHom.ker sk = s.asIdeal →
      (∀ c c' : Fin (2 * g) → Fin n,
        L'.finComb (Spec.map (CommRingCat.ofHom sk))
            (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P' i)) (fun i => (c i : ℕ)) =
          L'.finComb (Spec.map (CommRingCat.ofHom sk))
            (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P' i)) (fun i => (c' i : ℕ)) →
        c = c') ∧
      (∀ Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f',
        L'.nsmul (Spec.map (CommRingCat.ofHom sk)) n Q = L'.one (Spec.map (CommRingCat.ofHom sk)) →
        ∃ c : Fin (2 * g) → Fin n,
          L'.finComb (Spec.map (CommRingCat.ofHom sk))
            (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P' i)) (fun i => (c i : ℕ)) = Q)} =
      (Spec.map (CommRingCat.ofHom φ)).base ⁻¹' {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k),
        RingHom.ker sk = s.asIdeal →
        (∀ c c' : Fin (2 * g) → Fin n,
          L.finComb (Spec.map (CommRingCat.ofHom sk))
              (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c i : ℕ)) =
            L.finComb (Spec.map (CommRingCat.ofHom sk))
              (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c' i : ℕ)) →
          c = c') ∧
        (∀ Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f,
          L.nsmul (Spec.map (CommRingCat.ofHom sk)) n Q = L.one (Spec.map (CommRingCat.ofHom sk)) →
          ∃ c : Fin (2 * g) → Fin n,
            L.finComb (Spec.map (CommRingCat.ofHom sk))
              (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c i : ℕ)) = Q)} := by sorry
