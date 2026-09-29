-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_componentMap_frobenius_smul_eq_zero_of_eq_zero
-- name    : ModularCurve.PlaceSpecialization.componentMap_frobenius_smul_eq_zero_of_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/80cbb654-7ac6-5f34-82ae-35a119558ccd
-- title:
--   Frobenius stability of the kernel of the component map
-- statement:
--   Fix natural numbers $N \neq 0$ and $q$ with $q$ prime and $q \nmid N$, and a valuation subring $A$ of an algebraic closure $\bar{\mathbb{Q}}$ of $\mathbb{Q}$ lying over $q$, in the sense that $q$ is a nonunit of $A$; consequently the residue field $k = \mathrm{ResidueField}\,A$ has characteristic $q$, and the Hecke algebra $\mathbb{Z}[T_\ell]$ acts on $J_0(Nq)$ and on $J_0(N)$ through the modules `heckeModuleBar`. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,k\,N$ consisting exactly of the supersingular places, i.e. the rational places that are affine geometric and at which the value of the generator $\mathrm{jGeomGen}$ lies in the supersingular $j$-set for $q$; let the set of node pairs $S = \{(w, \Phi_q \cdot w) : w \in W\}$, for $\Phi_q = \mathrm{arithFrobC}\,q\,k\,N$ the semilinear automorphism induced by the $q$-power Frobenius on coefficients, be stable under $\Phi_q$ coordinatewise. Let `data` be a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating $(j, j_q)$, satisfying the Kronecker congruence $\Phi \equiv (X^q - Y)(X - Y^q)$ modulo $q$, and assume the two degeneracy maps $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ from level $N$ to level $Nq$ are integral. Let $P$ be a place specialisation at $A$ for these data, relative to the reduction map $A \to k$, $e$ a width function on places, $\mathrm{comp}$ an additive map from the inertia invariants of $J_0(Nq)$ (the classes fixed by the inertia subgroup of $A$ over $\mathbb{Q}$) to the component group of the Gram map attached to the widths $e$ on $S$, and $\mathrm{sp}$ an additive map from those inertia invariants to the glued $\mathrm{Pic}^0$ of $S$ over $k$; assume $\mathrm{comp}$ is surjective, that $\mathrm{comp}\,x = 0$ holds exactly when $x$ is a good class for $P$ and $S$ (it is represented by a degree-zero divisor whose support meets each node branch strictly and whose glue datum is admissible), and that $\mathrm{sp}$ is a glued specialisation for $P$ and $S$. The conclusion: for every $\varphi \in \mathrm{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})$ that is a Frobenius at $A$ for $q$, i.e. lies in the decomposition subgroup of $A$ and acts on $k$ as $x \mapsto x^q$, every inertia invariant $x$ whose translate $\varphi \cdot x$ is again inertia invariant, and with $\mathrm{comp}\,x = 0$, one has $\mathrm{comp}(\varphi \cdot x) = 0$.
--
--   This records the Frobenius-equivariance of the kernel of the map to the group of connected components of the special fibre at $q$, in the guise of the good-class condition: the property of being a good class is preserved by a Frobenius element at $A$. It is one of the component assertions of the existence statement packaging the semistable specialisation data of $J_0(Nq)$ at $q$ — all such components bind the same telescope of witnesses and their basic properties as hypotheses — and it feeds the decomposition-group version of the same stability and the comparison of the glued specialisation with `spPic0` under Frobenius translation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_componentMap_frobenius_smul_eq_zero_of_eq_zero.lean

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

theorem ModularCurve.PlaceSpecialization.componentMap_frobenius_smul_eq_zero_of_eq_zero (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
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
        (∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt φ q →
          ∀ (x : ↥(inertiaInvariants A (N * q)))
            (hx : φ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
            comp x = 0 → comp ⟨φ • (x : JZero (N * q)), hx⟩ = 0) := by sorry
