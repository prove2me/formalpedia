-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_torsion_preimage_componentMap_of_isModel
-- name    : ModularCurve.PlaceSpecialization.exists_torsion_preimage_componentMap_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/7ae1c8a9-f7bf-59d2-b976-5e387498f9e9
-- title:
--   Lifting m-torsion from the component group to inertia invariants
-- statement:
--   Fix a natural number $N \neq 0$ and a prime $q$ with $q \nmid N$, and a valuation subring $A$ of an algebraic closure of $\mathbb{Q}$ lying over $q$, in the sense that $q$ is a non-unit of $A$; its residue field $k$ then has characteristic $q$, and the degree-zero class groups $\mathrm{JZero}$ at levels $N$ and $Nq$ carry their Hecke-algebra module structures. Let $W$ be a finite set of places of the level-$N$ modular function field $\mathrm{modularFunctionFieldC}\ k\ N$ over $k$ consisting exactly of the supersingular places for $q$ and $N$, such that the set $\mathrm{nodePairsOfPlaces}$ of pairs $(w, \mathrm{Frob}\cdot w)$ attached to $W$ via the coefficientwise arithmetic Frobenius $\mathrm{arithFrobC}\ q\ k\ N$ is stable under that semilinear automorphism, i.e. contains $(g\cdot s_1, g\cdot s_2)$ for each of its members $s$. Let `data` be a modular polynomial datum for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ vanishing on the $q$-expansion pair) satisfying the Kronecker congruence, i.e. reducing modulo $q$ to $(C(X)^q - X)(C(X) - X^q)$, and assume the two degeneracy maps $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ from level $N$ to level $Nq$ are integral. Let $P$ be a `PlaceSpecialization` for these data, with $k$ and the residue map of $A$, and let $R$ be a `ProlongationTuple` for $P$ which is a model (the two divisor laws and the two cusp laws hold), satisfies the regularity law and the node value law for $W$, and satisfies the order law at Frobenius-fixed affine places. Let $e$ assign a width to each place, write $\Phi$ for the component group $\mathrm{componentGroup}$ of the induced widths on the node pairs (the dual of the character lattice modulo the image of the Gram map), and let $H$ be the subgroup of $\mathrm{JZero}(Nq)$ of elements fixed by the inertia subgroup of $A$ over $\mathbb{Q}$. Suppose given additive maps $\mathrm{comp} : H \to \Phi$ and $\mathrm{sp} : H \to \mathrm{GluedPic0}$ for the node pairs such that $\mathrm{comp}$ is surjective, $\mathrm{comp}\ x = 0$ holds precisely when $x$ is a good class for $P$ (the class of a degree-zero divisor supported on places strictly of the first or second kind whose glue datum is admissible), and $\mathrm{sp}$ is a glued specialization for $P$, i.e. sends the class of such a good divisor to the class of its glue datum. The conclusion is that for every natural number $m$ coprime to $q$ and every $\varphi \in \Phi$ with $m\varphi = 0$ there exists $x \in H$ with $mx = 0$ in $\mathrm{JZero}(Nq)$ and $\mathrm{comp}\ x = \varphi$.
--
--   This is the torsion-lifting step in the study of the component group of the Jacobian of $X_0(Nq)$ at a place above $q$: $m$-torsion of the combinatorial component group attached to the supersingular node pairs and their widths is realised by $m$-torsion inertia-invariant classes, for $m$ prime to $q$. It is used by the statements that assemble a width function, a component map and a glued specialization for given place data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_torsion_preimage_componentMap_of_isModel.lean

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

theorem ModularCurve.PlaceSpecialization.exists_torsion_preimage_componentMap_of_isModel (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
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
        (∀ m : ℕ, m.Coprime q →
          ∀ φ : componentGroup (widthOfPlaces (arithFrobC q (ResidueField A) N) W e),
            (m : ℤ) • φ = 0 →
              ∃ x : ↥(inertiaInvariants A (N * q)),
                (m : ℤ) • (x : JZero (N * q)) = 0 ∧ comp x = φ) := by sorry
