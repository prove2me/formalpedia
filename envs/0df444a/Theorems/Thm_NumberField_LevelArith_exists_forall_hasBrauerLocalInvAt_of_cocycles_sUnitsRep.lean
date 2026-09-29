-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_forall_hasBrauerLocalInvAt_of_cocycles_sUnitsRep
-- name    : NumberField.LevelArith.exists_forall_hasBrauerLocalInvAt_of_cocycles_sUnitsRep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/cdc6f8a4-0f45-5491-b221-27ba77656e94
-- title:
--   Presenting a p-primary S-Brauer class with prescribed local invariants
-- statement:
--   Fix a prime $p$ and a finite set $S$ of rational primes containing $p$, and let $L$ be an intermediate field of $\mathbb{Q}$ in $\overline{\mathbb{Q}}$, finite over $\mathbb{Q}$ and unramified outside $S$ (that is, finite over $\mathbb{Q}$, and for each prime $q \notin S$ and each valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ the corresponding inertia subgroup over $\mathbb{Q}$ lies in the fixing subgroup $\Gamma_L$ of $L$); if $p = 2$, assume $L$ contains a square root of $-1$. Let $F'' \supseteq L$ be a further intermediate field, finite and normal over $\mathbb{Q}$, unramified outside $S$, with $\mathrm{levelField}\,L\,F''$ (the extension of scalars of $F''$ to base $L$) Galois over $L$, and suppose given: a homomorphism $\iota''$ from $\mathrm{Gal}(\mathrm{levelField}\,L\,F''/L)$ to $\Gamma_L$ modulo the fixing subgroup of $F''$ intersected with $\Gamma_L$, splitting `levelGal` in the sense that $\iota''(\mathrm{levelGal}(g))$ is the class of $g$ for every $g \in \Gamma_L$; a morphism $\varphi''$ of representations from the $\iota''$-restriction of the quotient-to-invariants of `sUnitsMaxRep S L` by that subgroup to the $S$-unit representation `sUnitsRep` of $\mathrm{Gal}(\mathrm{levelField}\,L\,F''/L)$ at the places of $L$ above $S$, whose underlying map is bijective and compatible with the inclusions of values into $\overline{\mathbb{Q}}$; an idèle Galois descent $D''$ (a continuous action of the Galois group by ring automorphisms of the adèle ring of $\mathrm{levelField}\,L\,F''$ compatible with $\mathrm{algebraMap}$) whose induced action on idèle units agrees with a given `MulDistribMulAction`; and a morphism $j''$ from the $S$-unit representation to the idèle units whose underlying map is the principal-idèle map. Let $g$ be a $2$-cocycle of the $S$-unit representation whose class is killed by $p^k$, and let $t$ assign to each place $v$ of $L$ above $S$ an element of $\mathbb{R}/\mathbb{Z}$ such that the image of $[g]$ under $j''$ has local invariant $t(v)$ at $v$ in the sense of `HasLocalInv` for $D''$. Then there is a class $a$ in the $p$-power torsion part of $\mathrm{continuousH2Sr}$ of $\Gamma_L$ with coefficients in `sUnitsMaxRep S L` such that $\mathrm{HasBrauerLocalInvAt}\,p\,S\,L\,a\,v\,(t\,v)$ holds for every $v$, i.e. for each $v$ there exist a level $F$ with transport data $(\iota,\varphi)$, descent and principal-idèle data $(D,j)$, and a $2$-cocycle $f$ whose inflation represents $a$, with local invariant $t(v)$ at $v$.
--
--   This is the final transport step in the realisation of $p$-primary classes of the $S$-Brauer group of $\mathcal{O}_{L,S}$ in the presented form of `HasBrauerLocalInvAt`: a cocycle on a concrete Galois level with prescribed local invariants is converted into a class of the continuous $S$-ramified $H^2$ of $\Gamma_L$ together with a presentation witnessing those invariants. It is used by [`NumberField.LevelArith.exists_forall_hasBrauerLocalInvAt_of_ideleClass_hasLocalInv`](thm.html#NumberField.LevelArith.exists_forall_hasBrauerLocalInvAt_of_ideleClass_hasLocalInv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_forall_hasBrauerLocalInvAt_of_cocycles_sUnitsRep.lean

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
open CategoryTheory MonoidalCategory Module Limits groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField.LevelArith TensorProduct Pointwise
open scoped NumberField NumberField.PlaceDecomp
open M4aHerbrand

theorem NumberField.LevelArith.exists_forall_hasBrauerLocalInvAt_of_cocycles_sUnitsRep
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (F'' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF'' : L ≤ F'') [FiniteDimensional ℚ ↥F''] [Normal ℚ ↥F''] [IsGalois ↥L ↥(levelField L F'' hLF'')]
    (hF'' : F''.IsUnramifiedOutside S)
    (ι'' : (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) →* (↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (hι'' : ∀ g : ↥L.fixingSubgroup, ι'' (levelGal L F'' hLF'' g) = (g : ↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (φ'' : Rep.res ι'' ((sUnitsMaxRep S L).quotientToInvariants (F''.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
      NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S))
    (hφ'' : Function.Bijective φ''.hom)
    (hφ''val : ∀ x, ((NumberField.SUnits.val ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S) (φ''.hom x) : ↥(levelField L F'' hLF'')) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    (D'' : IdeleGaloisDescent (𝓞 ↥(levelField L F'' hLF'')) ↥L ↥(levelField L F'' hLF''))
    [MulDistribMulAction (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))ˣ]
    (hactI'' : ∀ (g : ↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) (y : (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))ˣ), g • y = D''.unitsAct g y)
    (j'' : NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S) ⟶
      Rep.ofMulDistribMulAction (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))ˣ)
    (hj'' : ∀ y, Additive.toMul (j''.hom y) =
      Units.map (algebraMap ↥(levelField L F'' hLF'') (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF'')) : ↥(levelField L F'' hLF'') →* AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))
        (NumberField.SUnits.val ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S) y))
    (g : cocycles₂ (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S)))
    (k : ℕ) (hk : (p ^ k : ℤ) • (H2π _ g) = 0)
    (t : ↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → AddCircle (1 : ℚ))
    (ht : ∀ v : ↥(placesOverPrimes ↥L (S : Set Nat.Primes)),
      NumberField.IdeleLocalInv.HasLocalInv ↥L ↥(levelField L F'' hLF'') D'' hactI'' ((groupCohomology.map (MonoidHom.id _) j'' 2) (H2π _ g)) v.1 (t v)) :
    ∃ a : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ))), ∀ v, HasBrauerLocalInvAt p S L a v (t v) := by sorry
