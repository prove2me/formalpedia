-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_primeToTorsion_spPic0_eq_of_primeToTorsion
-- name    : ModularCurve.PlaceSpecialization.exists_primeToTorsion_spPic0_eq_of_primeToTorsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/25f0507a-a9fc-50ea-9f9d-579cab2fa49d
-- title:
--   Prime-to-q torsion classes lift along `spPic0`
-- statement:
--   Let $N$ be a non-zero natural number and $q$ a prime not dividing $N$, and let $A$ be a valuation subring of an algebraic closure of $\mathbb{Q}$ satisfying `A.LiesOverPrime q`, i.e. the image of $q$ lies in the non-units of $A$; consequently the residue field $k$ of $A$ has characteristic $q$. With the Hecke-algebra module structures on `JZero (N * q)` and `JZero N` and the residue-field instances in place, the assertion is made for every finite set $W$ of places of `modularFunctionFieldC k N` whose members are exactly the supersingular places `ssPlaces q N k` (rational, affine geometric, with $j$-value in `ssJSet q`), such that the node-pair set obtained from $W$ by $w \mapsto (w, g\cdot w)$ for $g$ the coefficientwise Frobenius semilinear automorphism `arithFrobC q k N` is stable under $g$; for every modular polynomial datum `data` for $q$ satisfying the Kronecker congruence, every integrality hypothesis $h\alpha$, $h\beta$ for the two degeneracy maps at level $N$ and prime $q$, every place specialisation $P$ of level $N$ at $A$ over $k$ with reduction the residue map, every width function $e$ on places, and every pair of additive homomorphisms `comp` to the component group of the widths `widthOfPlaces` and `sp` to `GluedPic0`, with `comp` surjective, its kernel consisting exactly of the classes that are good for the node-pair set, and `sp` a glued specialisation for $P$. The conclusion: for every class $c$ in `Pic0 k (modularFunctionFieldC k N)` with $n \cdot c = 0$ for some $n > 0$ prime to $q$, there is $y \in$ `JZero N` with $m \cdot y = 0$ for some $m > 0$ prime to $q$ and `P.spPic0 y = c`.
--
--   This is the surjectivity of specialisation on prime-to-$q$ torsion for the Jacobian of $X_0(N)$ reduced at a place above $q \nmid N$, in the shape required by the multiplicity-one and component-group analysis at the auxiliary prime. It is one of the compatibilities bound under the common hypothesis telescope of [`ModularCurve.exists_width_comp_sp`](thm.html#ModularCurve.exists_width_comp_sp), which cites it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_primeToTorsion_spPic0_eq_of_primeToTorsion.lean

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.exists_primeToTorsion_spPic0_eq_of_primeToTorsion (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
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
      (e : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) → ℕ)
      (comp : ↥(inertiaInvariants A (N * q)) →+
        componentGroup (widthOfPlaces (arithFrobC q (ResidueField A) N) W e))
      (sp : ↥(inertiaInvariants A (N * q)) →+
        GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
          (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W))
      (hsurj : Function.Surjective comp)
      (hker : ∀ x : ↥(inertiaInvariants A (N * q)),
        comp x = 0 ↔ P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (x : JZero (N * q)))
      (hsp : P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) sp),
        (∀ c : Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N),
          PrimeToTorsion q c → ∃ y : JZero N, PrimeToTorsion q y ∧ P.spPic0 y = c) := by sorry
