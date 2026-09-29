-- Prove2me | Theorems.Thm_NumberField_IdeleLocalInv_exists_cocyclesTwo_sUnitsRep_hasLocalInv_of_map_pi_eq_zero_of_capitulation
-- name    : NumberField.IdeleLocalInv.exists_cocyclesTwo_sUnitsRep_hasLocalInv_of_map_pi_eq_zero_of_capitulation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/31f95964-4570-5896-b4f1-4e09ca195795
-- title:
--   Capitulation realises p-primary idèle classes by S-unit cocycles
-- statement:
--   Let $E\subseteq K\subseteq K''$ be number fields with $K/E$ and $K''/E$ Galois (the towers being compatible), and let $S$ be a finite set of height-one primes of $\mathcal{O}_E$. For $K$ one is given a descent datum $D$: a homomorphism from $\mathrm{Gal}(K/E)$ to the ring automorphisms of the adèle ring of $K$, acting continuously and compatibly with $\mathrm{Gal}(K/E)$ on $K$ via the structure map; the actions of $\mathrm{Gal}(K/E)$ on the idèle units and on the idèle class group (the units modulo the image of $K^\times$) are assumed to be those induced by $D$. Further data: for each finite place $w$ of $K$, a morphism $\mathrm{prG}\,w$ of representations of the decomposition subgroup $\mathrm{decomp}\,E\,K\,w$ from the restricted idèle units to $(K_w)^\times$ given on units by the $w$-component of the finite adèle part, and the quotient morphism $\pi$ onto the idèle class group. For $K''$ one is given a descent datum $D''$ (again inducing the given action) and a morphism $j''$ from the $S$-unit representation $\mathrm{sUnitsRep}\,E\,K''\,S$ (the subrepresentation of $\mathrm{Additive}\,(K'')^\times$ spanned by the $S$-units) to the idèle units of $K''$, given by the diagonal embedding. Let $p$ be prime and assume capitulation: whenever a nonzero $a\in\mathcal{O}_K$ and an ideal $I$ satisfy $I^{p^k}=(a)$, the extension of $I$ to $\mathcal{O}_{K''}$ is principal. Let $x\in H^2(\mathrm{Gal}(K/E),\mathbb{I}_K)$ satisfy $p^k\cdot x=0$ for some $k$, have vanishing image under $\mathrm{prG}\,w$ (and restriction to the decomposition group) for every $w$ whose contraction to $\mathcal{O}_E$ lies outside $S$, and vanishing image under $\pi$. The conclusion: there are a $2$-cocycle $f$ valued in $\mathrm{sUnitsRep}\,E\,K''\,S$ and an exponent $k'$ with $p^{k'}\cdot[f]=0$ such that for every height-one prime $v$ of $\mathcal{O}_E$ and every $t\in\mathbb{Q}/\mathbb{Z}$, if $x$ has local invariant $t$ at $v$ then so does the image of $[f]$ under $j''$ in $H^2(\mathrm{Gal}(K''/E),\mathbb{I}_{K''})$. Here "$x$ has local invariant $t$ at $v$" is the predicate $\mathrm{HasLocalInv}$: for some place $w$ of $K$ above $v$ and some residue characteristic $q$ of $w$, under an equivariant identification of $K_w$ with a finite extension $L'$ of $\mathbb{Q}_q$ inside a fixed algebraic closure, on which the decomposition group acts faithfully with fixed field a finite base $K_0$, the localisation of $x$ at $w$ equals $n$ times the image of a local fundamental class for that extension and $t=n/\#\mathrm{decomp}\,E\,K\,w$; the auxiliary identification and compatibility data are summarised here.
--
--   This is the surjective half of the Hasse principle for the Brauer-type computation of idèle cohomology: a $p$-primary degree-two idèle class supported over $S$ and trivial in the idèle class group is realised, with unchanged local invariants, by an $S$-unit $2$-cocycle of a layer in which the relevant ideals capitulate. It feeds [`NumberField.LevelArith.exists_forall_hasBrauerLocalInvAt_of_ideleClass_hasLocalInv`](thm.html#NumberField.LevelArith.exists_forall_hasBrauerLocalInvAt_of_ideleClass_hasLocalInv), where prescribed local invariants are transported to a finite-level cocycle with values in $S$-units.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_IdeleLocalInv_exists_cocyclesTwo_sUnitsRep_hasLocalInv_of_map_pi_eq_zero_of_capitulation.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_NumberField_IdeleLocalInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem NumberField.IdeleLocalInv.exists_cocyclesTwo_sUnitsRep_hasLocalInv_of_map_pi_eq_zero_of_capitulation
    (E K K'' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K''] [NumberField K'']
    [Algebra E K] [Algebra K K''] [Algebra E K''] [IsScalarTower E K K''] [IsGalois E K] [IsGalois E K'']
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

    (D'' : IdeleGaloisDescent (𝓞 K'') E K'')
    [MulDistribMulAction (K'' ≃ₐ[E] K'') (AdeleRing (𝓞 K'') K'')ˣ]
    (hactI'' : ∀ (g : K'' ≃ₐ[E] K'') (x : (AdeleRing (𝓞 K'') K'')ˣ), g • x = D''.unitsAct g x)
    (j'' : NumberField.SUnits.sUnitsRep E K'' S ⟶ Rep.ofMulDistribMulAction (K'' ≃ₐ[E] K'') (AdeleRing (𝓞 K'') K'')ˣ)
    (hj'' : ∀ y, Additive.toMul (j''.hom y) =
      Units.map (algebraMap K'' (AdeleRing (𝓞 K'') K'') : K'' →* AdeleRing (𝓞 K'') K'') (NumberField.SUnits.val E K'' S y))

    (p : ℕ) [Fact p.Prime]
    (hcap : ∀ (I : Ideal (𝓞 K)) (k : ℕ) (a : 𝓞 K), a ≠ 0 → I ^ p ^ k = Ideal.span {a} →
      (I.map (algebraMap (𝓞 K) (𝓞 K''))).IsPrincipal)

    (x : groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) 2)
    (k : ℕ) (hx : (p ^ k : ℤ) • x = 0)
    (hsupp : ∀ w : HeightOneSpectrum (𝓞 K), (∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) →
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E K w).subtype (prG w) 2).hom x = 0)
    (hπx : (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) π 2).hom x = 0) :
    ∃ (f : cocycles₂ (NumberField.SUnits.sUnitsRep E K'' S)) (k' : ℕ),
      (p ^ k' : ℤ) • (H2π _ f) = 0 ∧
      ∀ (v : HeightOneSpectrum (𝓞 E)) (t : AddCircle (1 : ℚ)),
        NumberField.IdeleLocalInv.HasLocalInv E K D hactI x v t →
        NumberField.IdeleLocalInv.HasLocalInv E K'' D'' hactI'' ((groupCohomology.map (MonoidHom.id (K'' ≃ₐ[E] K'')) j'' 2) (H2π _ f)) v t := by sorry
