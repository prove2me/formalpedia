-- Prove2me | Theorems.Thm_NumberField_IdeleLocalInv_exists_pow_smul_eq_zero_and_map_pi_eq_zero_and_hasLocalInv
-- name    : NumberField.IdeleLocalInv.exists_pow_smul_eq_zero_and_map_pi_eq_zero_and_hasLocalInv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/47c34e7b-8bd1-52bd-9fc9-aedc3662f5af
-- title:
--   Prescribed sum-zero local invariants on degree-two idèle cohomology
-- statement:
--   Let $E \subseteq K$ be number fields with $K/E$ Galois, let $S$ be a finite set of height-one primes of $\mathcal{O}_E$, and let $D$ be an idèle Galois descent datum for $\mathcal{O}_K, E, K$, i.e. a homomorphism from $\mathrm{Gal}(K/E) = (K \simeq_{\mathrm{alg}[E]} K)$ to the ring automorphisms of the adèle ring of $K$, continuous in each coordinate and compatible with the structure map from $K$. Assume the group $\mathrm{Gal}(K/E)$ acts multiplicatively and distributively on the idèles $(\mathbb{A}_K)^\times$ and on the idèle class group $(\mathbb{A}_K)^\times / \mathrm{principalIdeles}$ by the actions induced by $D$ (`D.unitsAct`, `D.classAct`). Given, for each finite place $w$ of $K$, a morphism $\mathrm{prG}\ w$ of representations of the decomposition subgroup $\mathrm{decomp}\,E\,K\,w$ (the decomposition subgroup of the valuation subring of $w$) from the restricted idèle representation to $(K_w)^\times$, computed on points by the $w$-component `finPart w` of the finite-adèle part, and a morphism $\pi$ of $\mathrm{Gal}(K/E)$-representations from the idèles to the idèle class group given by the quotient map; given a prime $p$ and $k \in \mathbb{N}$ with $p^k \mid \#\,\mathrm{decomp}\,E\,K\,(\mathrm{above}\,E\,K\,v)$ for every $v \in S$, and, when $p = 2$, with the stabiliser in $\mathrm{Gal}(K/E)$ of every infinite place of $K$ trivial; and given $t$ assigning to each finite place of $E$ an element of $\mathbb{Q}/\mathbb{Z}$ (written `AddCircle (1 : ℚ)`) with $p^k\, t_v = 0$ for all $v$, $t_v = 0$ for $v \notin S$ and $\sum_{v \in S} t_v = 0$. Then there is a class $x$ in degree-$2$ cohomology of $\mathrm{Gal}(K/E)$ with values in the idèles (taken additively) such that $p^k \cdot x = 0$; the local coordinate of $x$, i.e. its image under the map induced by the inclusion of $\mathrm{decomp}\,E\,K\,w$ and $\mathrm{prG}\ w$ in degree $2$, vanishes for every finite place $w$ of $K$ whose contraction to $\mathcal{O}_E$ is not the ideal of any $v \in S$; the image of $x$ under the map induced by $\pi$ in degree $2$ vanishes; and for each $v \in S$ the predicate $\mathrm{HasLocalInv}\,E\,K\,D\,x\,v\,t_v$ holds, that is, there exist a place $w$ of $K$ contracting to $v$, a prime $q$ with $q \in w$, a finite extension $L'$ of $\mathbb{Q}_q$ inside a fixed algebraic closure carrying a faithful action of $\mathrm{decomp}\,E\,K\,w$ fixing $\mathbb{Q}_q$, an equivariant ring isomorphism $\Phi \colon K_w \cong L'$, a finite base field $K_0 \subseteq L'$ which is exactly the fixed field of the action, a morphism $\theta$ of decomposition-group representations from $(L')^\times$ to $(K_w)^\times$ induced by $\Phi^{-1}$, a local fundamental class $u'$ in $H^2$ of $(L')^\times$ and an integer $n$ with the local coordinate of $x$ at $w$ equal to $n$ times the image of $u'$ under $\theta$, and $t_v$ the class of $n/\#\,\mathrm{decomp}\,E\,K\,w$ in $\mathbb{Q}/\mathbb{Z}$.
--
--   This is the idèle-theoretic half of the surjectivity of the $p$-primary Brauer-type invariant map onto the hyperplane of tuples of local invariants with zero sum: prescribed $p^k$-torsion local invariants summing to zero at the places of $S$ are realised by a single degree-two idèle class that is unramified outside $S$ and dies in the idèle class group. It is used by [`NumberField.LevelArith.exists_level_ideleClass_hasLocalInv_of_finsum_eq_zero`](thm.html#NumberField.LevelArith.exists_level_ideleClass_hasLocalInv_of_finsum_eq_zero) to produce classes at a suitable auxiliary layer.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_IdeleLocalInv_exists_pow_smul_eq_zero_and_map_pi_eq_zero_and_hasLocalInv.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_IdeleLocalInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain
open M4aHerbrand
open scoped NumberField.PlaceDecomp
open scoped NumberField.InfPlaceDecomp

theorem NumberField.IdeleLocalInv.exists_pow_smul_eq_zero_and_map_pi_eq_zero_and_hasLocalInv
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (D : IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (K ≃ₐ[E] K) (IdeleClassGroup (𝓞 K) K)]
    (hact : ∀ (g : K ≃ₐ[E] K) (c : IdeleClassGroup (𝓞 K) K), g • c = D.classAct g c)
    (prG : ∀ w : HeightOneSpectrum (𝓞 K),
      Rep.res (NumberField.PlaceDecomp.decomp E K w).subtype (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 K)) (y : (AdeleRing (𝓞 K) K)ˣ), (prG w).hom (Additive.ofMul y) = Additive.ofMul (finPart w y))
    (π : Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (IdeleClassGroup (𝓞 K) K))
    (hπ : ∀ y : (AdeleRing (𝓞 K) K)ˣ, π.hom (Additive.ofMul y) = Additive.ofMul (QuotientGroup.mk y : IdeleClassGroup (𝓞 K) K))
    (p : ℕ) [Fact p.Prime] (k : ℕ)
    (hdeg : ∀ v ∈ S, p ^ k ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v)))
    (hinf2 : p = 2 → ∀ (v : InfinitePlace K) (g : K ≃ₐ[E] K), g ∈ NumberField.InfPlaceDecomp.decomp E K v → g = 1)
    (t : HeightOneSpectrum (𝓞 E) → AddCircle (1 : ℚ))
    (htp : ∀ v, (p ^ k : ℤ) • t v = 0) (ht0 : ∀ v, v ∉ S → t v = 0) (hts : ∑ v ∈ S, t v = 0) :
    ∃ x : groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) 2,
      (p ^ k : ℤ) • x = 0 ∧
      (∀ w : HeightOneSpectrum (𝓞 K), (∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) →
        (groupCohomology.map (NumberField.PlaceDecomp.decomp E K w).subtype (prG w) 2).hom x = 0) ∧
      (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) π 2).hom x = 0 ∧
      ∀ v ∈ S, NumberField.IdeleLocalInv.HasLocalInv E K D hactI x v (t v) := by sorry
