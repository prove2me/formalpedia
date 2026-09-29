-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_gluedSpecialization_nodeUnit_heckeGen_eq_nodePerm_symm_comp
-- name    : ModularCurve.PlaceSpecialization.gluedSpecialization_nodeUnit_heckeGen_eq_nodePerm_symm_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/dbbd6253-3c6e-5d0c-86f4-985cd1271178
-- title:
--   Hecke action at q on node units of the glued specialisation
-- statement:
--   Let $N$ be a nonzero natural number, $q$ a prime not dividing $N$, and $A$ a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that $q$ is a nonunit of $A$; its residue field $\kappa$ then has characteristic $q$, and $J_0(M)=\mathrm{Pic}^0$ of the level-$M$ modular function field over $\overline{\mathbb{Q}}$ carries the module structure over the polynomial Hecke algebra $\mathbb{Z}[X_\ell : \ell \text{ prime}]$ given by `heckeModuleBar`. Fix a finite set $W$ of places of the level-$N$ modular function field $F_N$ over $\kappa$ whose members are exactly the supersingular places (rational, affine geometric, with $j$-value in the supersingular set for $q$), put $S=\{(w,\mathrm{Frob}\cdot w): w\in W\}$ for the coefficientwise arithmetic Frobenius semilinear automorphism $\mathrm{Frob}=$ `arithFrobC`, and assume $S$ is stable under $\mathrm{Frob}$ acting coordinatewise, giving the permutation $\pi$ of $S$ sending $(w_1,w_2)$ to $(\mathrm{Frob}\cdot w_1,\mathrm{Frob}\cdot w_2)$. Fix further modular polynomial data for $q$ satisfying the Kronecker congruence, integrality of both degeneracy maps $\alpha,\beta$ from level $N$ to level $Nq$, a `PlaceSpecialization` datum $P$ for $A$, $q$, $N$ with reduction map $A\to\kappa$, a width function $e$ on places, and additive maps $\mathrm{comp}$ from the inertia invariants $H=J_0(Nq)^{I_A}$ to the component group of the widths of $S$ and $\mathrm{sp}\colon H\to \mathrm{GluedPic}^0(\kappa,F_N,S)$, subject to: $\mathrm{comp}$ is surjective, $\mathrm{comp}(x)=0$ holds exactly when $x$ is a good class for $P$ and $S$ (the class of a degree-zero divisor supported at strictly-first or strictly-second points whose glue datum is admissible), and $\mathrm{sp}$ is a glued specialisation for $P$ and $S$. Then for every $x\in H$ such that $X_q\cdot x$ again lies in $H$, if $\mathrm{comp}(x)=0$ and $\mathrm{sp}(x)$ is the node-unit class of a family $u\colon S\to \mathrm{Additive}\,\kappa^\times$, then $\mathrm{sp}(X_q\cdot x)$ is the node-unit class of $u\circ\pi^{-1}$.
--
--   This is the computation of the Hecke operator at $q$ on the toric part of the specialisation of $J_0(Nq)$ at $q$: on classes coming from node units of the glued degree-zero class group of the two copies of the level-$N$ curve, $X_q$ acts by precomposition with the inverse of the Frobenius permutation of the node pairs. It feeds the statements that assemble a full specialisation datum together with its width, component-group and node-value laws, and thence the level-lowering argument at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_gluedSpecialization_nodeUnit_heckeGen_eq_nodePerm_symm_comp.lean

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

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.gluedSpecialization_nodeUnit_heckeGen_eq_nodePerm_symm_comp (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
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
        (∀ (x : ↥(inertiaInvariants A (N * q)))
            (hx : heckeGen ⟨q, hq⟩ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
            comp x = 0 →
              ∀ u : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) →
                  Additive (ResidueField A)ˣ,
                sp x = GluedPic0.nodeUnit
                    (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) u →
                  sp ⟨heckeGen ⟨q, hq⟩ • (x : JZero (N * q)), hx⟩ =
                    GluedPic0.nodeUnit (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                      (fun t => u ((SemilinearAut.nodePerm
                        (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                        (arithFrobC q (ResidueField A) N) hstab).symm t))) := by sorry
