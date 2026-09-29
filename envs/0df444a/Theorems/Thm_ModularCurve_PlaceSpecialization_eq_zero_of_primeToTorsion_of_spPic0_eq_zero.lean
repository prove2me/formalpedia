-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_eq_zero_of_primeToTorsion_of_spPic0_eq_zero
-- name    : ModularCurve.PlaceSpecialization.eq_zero_of_primeToTorsion_of_spPic0_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/c12897eb-7fb8-57ec-8e2b-7cdbaac2fac2
-- title:
--   Injectivity of `spPic0` on prime-to-q torsion
-- statement:
--   Fix natural numbers $N \ne 0$ and $q$ with $q$ prime and $q \nmid N$, and a valuation subring $A$ of an algebraic closure of $\mathbb{Q}$ satisfying `A.LiesOverPrime q`, i.e. the image of $q$ lies in the non-units of $A$; consequently the residue field $k =$ `ResidueField A` has characteristic $q$. The assertion is then universally quantified over the following data: a finite set $W$ of places of the function field `modularFunctionFieldC k N` over $k$ whose members are exactly the supersingular places `ssPlaces q N k` (rational affine geometric places whose $j$-value lies in `ssJSet q k`); the hypothesis that the set of node pairs `nodePairsOfPlaces (arithFrobC q k N) W`, obtained by pairing each $w \in W$ with its image under the semilinear automorphism induced by the Frobenius of $k$, is stable under that automorphism in the sense that it contains $(g \cdot s_1, g \cdot s_2)$ for each of its members $s$; modular polynomial data `data` for $q$ satisfying the Kronecker congruence, that the reduction of $\Phi$ modulo $q$ equals $(Y^q - X)(Y - X^q)$; integrality of the two Hecke maps $\alpha$, $\beta$ between the base-changed modular function fields of levels $N$ and $Nq$ over $\overline{\mathbb{Q}}$; a place specialisation $P$ of type `PlaceSpecialization A q N data hKr k (IsLocalRing.residue A) h\alpha h\beta`; a width function $e$ on places; additive maps `comp` and `sp` from the inertia invariants of `JZero (N * q)` (the classes in the degree-zero divisor class group of the level-$Nq$ base-changed modular function field fixed by the inertia subgroup of $A$ over $\mathbb{Q}$) to, respectively, the component group attached to the widths `widthOfPlaces (arithFrobC q k N) W e` and the glued Picard group `GluedPic0` of the above node pairs; surjectivity of `comp`; the statement that `comp x` vanishes exactly when the underlying class of $x$ is a good class for $P$ relative to those node pairs; and the statement that `sp` is a glued specialisation for $P$ relative to those node pairs. Under all of this, for every $y$ in `JZero N` which is prime-to-$q$ torsion, i.e. $n \cdot y = 0$ for some $n > 0$ with $q \nmid n$, and which satisfies `P.spPic0 y = 0`, one has $y = 0$.
--
--   This is the classical injectivity of reduction modulo a prime of residue characteristic $q$ on the prime-to-$q$ torsion of the Jacobian $J_0(N)$, here in the form that the specialisation map `spPic0` attached to a place specialisation kills no non-zero prime-to-$q$ torsion class. It is one component of the packaged existence statement [`ModularCurve.exists_width_comp_sp`](thm.html#ModularCurve.exists_width_comp_sp), and for that reason carries the full list of hypotheses (node data, widths, component map and glued specialisation) shared by the components of that package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_eq_zero_of_primeToTorsion_of_spPic0_eq_zero.lean

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

theorem ModularCurve.PlaceSpecialization.eq_zero_of_primeToTorsion_of_spPic0_eq_zero (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
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
        (∀ y : JZero N, PrimeToTorsion q y → P.spPic0 y = 0 → y = 0) := by sorry
