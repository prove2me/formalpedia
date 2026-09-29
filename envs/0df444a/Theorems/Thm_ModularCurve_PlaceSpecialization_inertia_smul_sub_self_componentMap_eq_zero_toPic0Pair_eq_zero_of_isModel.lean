-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_inertia_smul_sub_self_componentMap_eq_zero_toPic0Pair_eq_zero_of_isModel
-- name    : ModularCurve.PlaceSpecialization.inertia_smul_sub_self_componentMap_eq_zero_toPic0Pair_eq_zero_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/75317eb1-e99e-54d4-87b5-964d160636c6
-- title:
--   Inertia differences on prime-to-q torsion are toric
-- statement:
--   Fix a positive integer $N$ and a prime $q$ with $q \nmid N$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $q$, i.e. with $q$ a non-unit of $A$, so that $\mathrm{ResidueField}\,A$ has characteristic $q$. The assertion is universally quantified over the following data: a finite set $W$ of places of the level-$N$ modular function field $\mathtt{modularFunctionFieldC}(\mathrm{ResidueField}\,A)\,N$ whose members are exactly the supersingular places `ssPlaces q N`; the hypothesis that the node-pair set $S=\mathtt{nodePairsOfPlaces}$ attached to $W$ and to the arithmetic Frobenius semilinear automorphism $\mathtt{arithFrobC}\,q$ (the image of $W$ under $w \mapsto (w,\ \mathtt{arithFrobC} \cdot w)$) is stable under $\mathtt{arithFrobC}\,q$, in the sense that $(g\cdot s_1, g\cdot s_2)\in S$ for every $s\in S$; a modular polynomial datum `data` for $q$ (a monic $\Phi$ of degree $\psi(q)$ killing the pair $(j,j_q)$) satisfying the Kronecker congruence $\Phi \equiv (C X^q - X)(C X - X^q) \pmod q$; integrality of the two degeneracy embeddings $\mathtt{heckeAlphaBar}$ and $\mathtt{heckeBetaBar}$ from level $N$ to level $Nq$; a place specialisation $P$ over $A$ with values in $\mathrm{ResidueField}\,A$ and reduction map the residue map of $A$; a prolongation tuple $R$ for $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws), the regularity law and the node-value law for $W$, and the order law at Frobenius-fixed affine places; a width function $e$ on places; additive maps $\mathrm{comp}$ from the inertia invariants $\mathtt{inertiaInvariants}\,A\,(Nq)$ (the elements of $\mathrm{JZero}(Nq) = \mathrm{Pic}^0$ of the level-$Nq$ modular function field over $\overline{\mathbb{Q}}$ fixed by the inertia subgroup of $A$ inside $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$) to the component group of the widths $s \mapsto e(s_1)$ on $S$, and $\mathrm{sp}$ from the same source to the glued degree-zero class group $\mathtt{GluedPic0}$ of $S$; surjectivity of $\mathrm{comp}$; the requirement that $\mathrm{comp}\,x = 0$ holds exactly when the class of $x$ is good, that is, represented by a degree-zero divisor supported on places strict for the first or second reduction of $P$ whose glue datum is admissible; and the requirement that $\mathrm{sp}$ be a glued specialisation, computing on such good representatives the class of their glue datum. Under all of these, for every $\sigma$ in the inertia subgroup of $A$ over $\mathbb{Q}$ and every $x \in \mathrm{JZero}(Nq)$ annihilated by some positive integer prime to $q$, the difference $\sigma \cdot x - x$ lies in $\mathtt{inertiaInvariants}\,A\,(Nq)$, its image under $\mathrm{comp}$ vanishes, and the image of $\mathrm{sp}(\sigma \cdot x - x)$ under $\mathtt{GluedPic0.toPic0Pair}$, the projection of a glued class to the pair of $\mathrm{Pic}^0$ classes of its two divisors, vanishes as well.
--
--   This is the unipotence statement for the action of inertia at $q$ on the prime-to-$q$ torsion of the Jacobian of $X_0(Nq)$, in the form needed on the geometric side of level lowering: monodromy differences $\sigma x - x$ are inertia-invariant and land in the toric part, having trivial component class and trivial pair of $\mathrm{Pic}^0$ classes. It feeds the extraction of the toric monodromy part in the component group and the downstream existence statements assembling place specialisations with widths, component maps and glued specialisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_inertia_smul_sub_self_componentMap_eq_zero_toPic0Pair_eq_zero_of_isModel.lean

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.inertia_smul_sub_self_componentMap_eq_zero_toPic0Pair_eq_zero_of_isModel (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
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
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ) (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed)
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
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : JZero (N * q),
          PrimeToTorsion q x →
            ∃ h : σ • x - x ∈ inertiaInvariants A (N * q),
              comp ⟨σ • x - x, h⟩ = 0 ∧
                GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (sp ⟨σ • x - x, h⟩) = 0) := by sorry
