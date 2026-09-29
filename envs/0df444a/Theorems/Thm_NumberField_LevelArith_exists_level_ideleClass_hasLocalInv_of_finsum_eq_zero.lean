-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_level_ideleClass_hasLocalInv_of_finsum_eq_zero
-- name    : NumberField.LevelArith.exists_level_ideleClass_hasLocalInv_of_finsum_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/2de73374-96ae-51f3-b5de-7be9fe2a1c91
-- title:
--   Realising p-primary sum-zero families as local invariants of idèle classes
-- statement:
--   Let $p$ be a prime and $S$ a finite set of rational primes containing $p$. Let $L$ be an intermediate field of $\mathbb{Q}$ in $\overline{\mathbb{Q}}$, finite over $\mathbb{Q}$, which is unramified outside $S$ in the sense that $L$ is finite over $\mathbb{Q}$ and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, the inertia subgroup of $A$ over $\mathbb{Q}$ lies in the fixing subgroup of $L$; assume moreover that if $p = 2$ then $L$ contains a square root of $-1$. Let $f$ assign to each height-one prime $w$ of $\mathcal{O}_L$ containing some member of $S$ an element of $\mathbb{Q}/\mathbb{Z}$, suppose each $f(w)$ is killed by some power $p^k$, and suppose the (finitely supported) sum $\sum_w f(w)$ vanishes. Then there exist an intermediate field $F \supseteq L$, finite and normal over $\mathbb{Q}$ and unramified outside $S$ in the same sense, such that $K := F$ viewed over $L$ is Galois over $L$, together with: an idèle Galois descent datum $D$ for $K/L$, that is a monoid homomorphism from $\mathrm{Gal}(K/L)$ to ring automorphisms of the adèle ring $\mathbb{A}_K$ which is continuous and compatible with the Galois action on $K$; actions of $\mathrm{Gal}(K/L)$ on $\mathbb{A}_K^\times$ and on the idèle class group $\mathbb{A}_K^\times/K^\times$ given by $D$; for each finite place $w$ of $K$ a morphism $\mathrm{prG}\,w$ of representations of the decomposition subgroup $G_w$ of $w$ over $L$, from the restriction of $\mathbb{A}_K^\times$ to $(K_w)^\times$, inducing $y \mapsto y_w$; a morphism $\pi$ of $\mathrm{Gal}(K/L)$-representations $\mathbb{A}_K^\times \to \mathbb{A}_K^\times/K^\times$ inducing the quotient map; and a class $x \in H^2(\mathrm{Gal}(K/L), \mathbb{A}_K^\times)$ and $k \in \mathbb{N}$ such that $p^k x = 0$; the localisation of $x$ along $G_w \hookrightarrow \mathrm{Gal}(K/L)$ and $\mathrm{prG}\,w$ vanishes for every $w$ whose contraction to $\mathcal{O}_L$ is not one of the places of $L$ above $S$; the image of $x$ under $H^2(\pi)$ vanishes; and for each place $v$ of $L$ above $S$ the predicate [`NumberField.IdeleLocalInv.HasLocalInv`](def/NumberField_IdeleLocalInvariant.html#L14) holds for $x$, $v$ and $f(v)$, that is there are a place $w$ of $K$ contracting to $v$, a residue characteristic $q$ with $q \in w$, a finite extension $L'$ of $\mathbb{Q}_q$ with a faithful $G_w$-action and a $G_w$-equivariant ring isomorphism $K_w \cong L'$ over $\mathbb{Q}_q$, a base field $K_0 \le L'$ cut out as the $G_w$-fixed elements of $L'$, a comparison morphism $\theta$ of $G_w$-representations $(L')^\times \to (K_w)^\times$ realising the inverse isomorphism, a local fundamental class $u'$ in $H^2(G_w, (L')^\times)$ in the sense of [`ExtCitation.LocalLevel.IsLocalFundamentalClass`](def/ExtCitation_LocalLevel_FundamentalClass.html#L60), and an integer $n$, such that the localisation of $x$ at $w$ equals $n$ times the image of $u'$ under $\theta$ and $f(v)$ is the class of $n/\#G_w$ in $\mathbb{Q}/\mathbb{Z}$.
--
--   This is the idèle-theoretic half of the surjectivity statement for local invariants: any $p$-primary family of elements of $\mathbb{Q}/\mathbb{Z}$ indexed by the places of $L$ above $S$ and summing to zero is realised by an idèle cohomology class over a suitable finite Galois level, unramified outside $S$, which dies in the idèle class group and is unramified away from $S$. It feeds [`NumberField.LevelArith.mem_range_of_isBrauerLocalInv_of_finsum_eq_zero`](thm.html#NumberField.LevelArith.mem_range_of_isBrauerLocalInv_of_finsum_eq_zero), where such a class is transferred to the $p$-primary Brauer group of the $S$-integers of $L$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_level_ideleClass_hasLocalInv_of_finsum_eq_zero.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_IdeleLocalInvariant
import Definitions.Def_NumberField_BrauerLocalInvariantChar
import Definitions.Def_NumberField_BrauerLocalInvariantPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.MonoidalCategory Module CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits groupCohomology ExtCitation
open NumberField.LevelArith
open scoped Classical NumberField.LevelArith TensorProduct Pointwise
open scoped NumberField NumberField.PlaceDecomp
open M4aHerbrand
open IsDedekindDomain

theorem NumberField.LevelArith.exists_level_ideleClass_hasLocalInv_of_finsum_eq_zero
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (f : ↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → AddCircle (1 : ℚ))
    (hfp : ∀ w, ∃ k : ℕ, (p ^ k : ℤ) • f w = 0) (hfs : ∑ᶠ w, f w = 0) :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) (_ : FiniteDimensional ℚ ↥F) (_ : Normal ℚ ↥F)
      (_ : IsGalois ↥L ↥(levelField L F hLF)) (_ : F.IsUnramifiedOutside S)
      (D : IdeleGaloisDescent (𝓞 ↥(levelField L F hLF)) ↥L ↥(levelField L F hLF))
      (_ : MulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)
      (hactI : ∀ (g : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) (y : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ), g • y = D.unitsAct g y)
      (_ : MulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)))
      (_ : ∀ (g : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) (c : (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))), g • c = D.classAct g c)
      (prG : ∀ w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF)),
        Rep.res (NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w).subtype (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w)) (w.adicCompletion ↥(levelField L F hLF))ˣ)
      (_ : ∀ (w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF))) (y : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ), (prG w).hom (Additive.ofMul y) = Additive.ofMul (finPart w y))
      (π : Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ ⟶ Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)))
      (_ : ∀ y : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ, π.hom (Additive.ofMul y) = Additive.ofMul (QuotientGroup.mk y : (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))))
      (x : groupCohomology (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) 2) (k : ℕ),
      (p ^ k : ℤ) • x = 0 ∧
      (∀ w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF)), (∀ v ∈ placesOverPrimesFinset ↥L S, w.asIdeal.comap (algebraMap (𝓞 ↥L) (𝓞 ↥(levelField L F hLF))) ≠ v.asIdeal) →
        (groupCohomology.map (NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w).subtype (prG w) 2).hom x = 0) ∧
      (groupCohomology.map (MonoidHom.id (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) π 2).hom x = 0 ∧
      ∀ v : ↥(placesOverPrimes ↥L (S : Set Nat.Primes)), NumberField.IdeleLocalInv.HasLocalInv ↥L ↥(levelField L F hLF) D hactI x v.1 (f v) := by sorry
