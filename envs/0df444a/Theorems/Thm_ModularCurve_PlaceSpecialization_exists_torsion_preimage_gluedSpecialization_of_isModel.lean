-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_torsion_preimage_gluedSpecialization_of_isModel
-- name    : ModularCurve.PlaceSpecialization.exists_torsion_preimage_gluedSpecialization_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/64e35826-0899-5dbf-9dc0-f8a1c3d46864
-- title:
--   Lifting m-torsion through the glued specialization at q
-- statement:
--   Let $N$ be a positive integer and $q$ a prime not dividing $N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that $q$ is a non-unit of $A$; its residue field $\kappa$ then has characteristic $q$. Fix a finite set $W$ of places of the level-$N$ modular function field $\mathrm{modularFunctionFieldC}\ \kappa\ N$ whose members are exactly the supersingular places `ssPlaces q N κ`, and assume the finite set $\Sigma$ of node pairs $(w,\ \mathrm{arithFrobC}\cdot w)$ indexed by $w\in W$ is stable under the arithmetic Frobenius semilinear automorphism $\mathrm{arithFrobC}\ q\ \kappa\ N$, in the sense that it contains $(g\cdot s_1,g\cdot s_2)$ for each of its members $s$. Fix modular polynomial data for $q$ satisfying the Kronecker congruence (its reduction modulo $q$ is $(C X^q-X)(C X-X^q)$), integrality of the two degeneracy embeddings $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$, a place-specialization datum $P$ over $A$ with reduction map the residue map of $A$, and a prolongation tuple $R$ for $P$ which is a model (the two divisor laws and the two cusp laws hold) and satisfies the regularity law and node-value law for $W$ and the fixed-point order law. Let $e$ assign a width to each place, let $H$ denote the subgroup of $\mathrm{JZero}(Nq)=\mathrm{Pic}^0(\mathrm{modularFunctionFieldBar}(Nq))$ of elements fixed by the inertia subgroup of $A$ over $\mathbb{Q}$, and let $\mathrm{comp}:H\to\Phi$ and $\mathrm{sp}:H\to\mathrm{GluedPic}^0(\kappa,\ \mathrm{modularFunctionFieldC}\ \kappa\ N,\ \Sigma)$ be additive maps into the combinatorial component group of the widths of $\Sigma$ and into the glued degree-zero class group, subject to: $\mathrm{comp}$ is surjective, $\mathrm{comp}\,x=0$ holds exactly when the class of $x$ is a good class for $\Sigma$, and $\mathrm{sp}$ is a glued specialization for $\Sigma$. Then for every $m$ coprime to $q$ and every $g$ in the glued degree-zero class group with $m\cdot g=0$ there is $x\in H$ with $m\cdot x=0$ in $\mathrm{JZero}(Nq)$, $\mathrm{comp}\,x=0$ and $\mathrm{sp}\,x=g$.
--
--   This is the torsion-lifting step for the specialization of $J_0(Nq)$ at a place above $q$: $m$-torsion in the glued degree-zero class group of the special fibre, for $m$ prime to $q$, is realised by $m$-torsion inertia-invariant classes lying in the identity component. It is used by the existence statements that package a place-specialization datum together with widths, component map and glued specialization.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_torsion_preimage_gluedSpecialization_of_isModel.lean

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

theorem ModularCurve.PlaceSpecialization.exists_torsion_preimage_gluedSpecialization_of_isModel (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
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
          ∀ g : GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
              (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W),
            (m : ℤ) • g = 0 →
              ∃ x : ↥(inertiaInvariants A (N * q)),
                (m : ℤ) • (x : JZero (N * q)) = 0 ∧ comp x = 0 ∧ sp x = g) := by sorry
