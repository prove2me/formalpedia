-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_widths_componentMap_gluedSpecialization_placeWidthChar_correspondence_heckeComponentAction_agree_of_isModel
-- name    : ModularCurve.PlaceSpecialization.exists_widths_componentMap_gluedSpecialization_placeWidthChar_correspondence_heckeComponentAction_agree_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/ece6ea05-4e6c-5a56-b2a0-150a25e42ccc
-- title:
--   Widths, component map, glued specialisation and Hecke matrices
-- statement:
--   Let $N \geq 1$ and let $q$ be a prime with $q \nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, so that the residue field $k = \mathrm{ResidueField}\,A$ has characteristic $q$; the groups $\mathrm{JZero}\,(Nq)$ and $\mathrm{JZero}\,N$ carry the Hecke-algebra module structures `heckeModuleBar`. Fix a finite set $W$ of places of $\mathrm{modularFunctionFieldC}\,k\,N$ whose members are exactly the places in $\mathrm{ssPlaces}\,q\,N\,k$, such that the finite set $S = \mathrm{nodePairsOfPlaces}$ of pairs $(w, \mathrm{arithFrobC}\,q\,k\,N \cdot w)$ for $w \in W$ is stable under the arithmetic Frobenius semilinear automorphism; fix modular polynomial data for $q$ satisfying the Kronecker congruence, integrality of the two level-$N$, prime-$q$ degeneracy maps over $\overline{\mathbb{Q}}$, a place specialisation $P$ over the reduction $A \to k$, and a prolongation tuple $R$ for $P$ satisfying `IsModel`, `OrderLawFixed`, and the regularity and node-value laws at $W$. Then there exist a width function $e$ on places, an additive map $\mathrm{comp}$ from the inertia invariants of $\mathrm{JZero}\,(Nq)$ to the component group of the weights $\mathrm{widthOfPlaces}$ attached to $S$ and $e$, an additive map $\mathrm{sp}$ to $\mathrm{GluedPic0}\,k\,(\mathrm{modularFunctionFieldC}\,k\,N)\,S$, and integer matrices $B_\ell$ indexed by $S \times S$, one for each prime $\ell$, with all row sums of $B_\ell$ equal to $\ell + 1$ and $e_j B_\ell(i,j) = e_i B_\ell(j,i)$, such that: $e$ is positive on $W$ and agrees on $W$ with $\mathrm{placeWidthChar}\,q\,N$; $\mathrm{comp}$ is surjective and its kernel consists exactly of the classes satisfying $P.\mathrm{IsGoodClass}\,S$; $\mathrm{sp}$ satisfies $P.\mathrm{IsGluedSpecialization}\,S$; and for every prime $\ell \nmid Nq$, the weight $e_i$ divides the off-diagonal entries $B_\ell(i,j)$, the map $\mathrm{comp}$ intertwines the action of $\mathrm{heckeGen}\,\ell$ on those inertia invariants $x$ with $\mathrm{heckeGen}\,\ell \cdot x$ again invariant with $\mathrm{heckeComponentAction}$ of $B_\ell$, and, assuming principal divisors exist on the degeneracy roof $\mathrm{charLDegeneracyRoof}\,k\,N\,\ell$ and integrality of the two characteristic-$q$ degeneracy maps at $\ell$, the entry $B_\ell(t,s)$ is the coefficient at the first place of $s$ of the divisor correspondence attached to these two maps applied to the divisor $\mathrm{single}$ at the first place of $t$.
--
--   This assembles, for the semistable reduction of $J_0(Nq)$ at $q$, the component group of the $e$-weighted dual graph of supersingular node pairs together with the specialisation map and the matrices describing the Hecke action on it, identifying those matrices with Hecke correspondence multiplicities on the characteristic-$q$ modular curve. It is used by [`ModularCurve.PlaceSpecialization.componentMap_heckeGen_smul_eq_add_one_smul_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.componentMap_heckeGen_smul_eq_add_one_smul_of_isModel), where the divisibility and row-sum properties force $T_\ell$ to act on the component group as multiplication by $\ell + 1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_widths_componentMap_gluedSpecialization_placeWidthChar_correspondence_heckeComponentAction_agree_of_isModel.lean

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_ComponentGroupHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option Elab.async false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.exists_widths_componentMap_gluedSpecialization_placeWidthChar_correspondence_heckeComponentAction_agree_of_isModel
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := heckeModuleBar (N * q)
    letI := heckeModuleBar N
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (hstab : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (arithFrobC q (ResidueField A) N))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel) (hO : R.OrderLawFixed)
      (hreg : R.RegularityLaw W) (hnv : R.NodeValueLaw W),
      ∃ (e : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) → ℕ)
        (comp : ↥(inertiaInvariants A (N * q)) →+
          componentGroup (widthOfPlaces (arithFrobC q (ResidueField A) N) W e))
        (sp : ↥(inertiaInvariants A (N * q)) →+
          GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
            (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W))
        (B : Nat.Primes → Matrix ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
          ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) ℤ)
        (hrow : ∀ ℓ, HeckeRowSums (B ℓ) (((ℓ : ℕ) : ℤ) + 1))
        (hsym : ∀ ℓ, HeckeWeightSymm (widthOfPlaces (arithFrobC q (ResidueField A) N) W e) (B ℓ)),
        (∀ w ∈ W, 0 < e w) ∧
        Function.Surjective comp ∧
        (∀ x : ↥(inertiaInvariants A (N * q)),
          comp x = 0 ↔ P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (x : JZero (N * q))) ∧
        P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) sp ∧
        (∀ w ∈ W, e w = placeWidthChar q N w) ∧
        (∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ N * q →
          HeckeOffDiagDivides (widthOfPlaces (arithFrobC q (ResidueField A) N) W e) (B ℓ)) ∧
        (∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ N * q →
          ∀ (x : ↥(inertiaInvariants A (N * q)))
            (hx : heckeGen ℓ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
            comp ⟨heckeGen ℓ • (x : JZero (N * q)), hx⟩ =
              heckeComponentAction (widthOfPlaces (arithFrobC q (ResidueField A) N) W e)
                (B ℓ) (hrow ℓ) (hsym ℓ) (comp x)) ∧
        (∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ N * q →
          (haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩;
          ∀ [HasPrincipalDivisors (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ)]
          (hαc : HeckeAlphaCIntegral (ResidueField A) N ℓ) (hβc : HeckeBetaCIntegral (ResidueField A) N ℓ)
          (s t : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)),
          B ℓ t s = Divisor.correspondence (heckeAlphaC (ResidueField A) N ℓ)
          (heckeBetaC (ResidueField A) N ℓ) hαc hβc (Finsupp.single t.1.1 1) s.1.1)) := by sorry
