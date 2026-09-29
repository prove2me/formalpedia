-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_gluedMk_eq_nodeUnit_of_isGoodDiv_of_admissible_of_pic0Mk_eq_smul_single_sub_self_of_isModel
-- name    : ModularCurve.PlaceSpecialization.exists_gluedMk_eq_nodeUnit_of_isGoodDiv_of_admissible_of_pic0Mk_eq_smul_single_sub_self_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/9bde216f-3bf1-5111-8e61-90c344beee1c
-- title:
--   Inertial displacements at non-strict supersingular places give node units
-- statement:
--   Let $N\ge 1$ and let $q$ be a prime with $q\nmid N$, let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $q$ (that is, $q$ is a non-unit of $A$, whence the residue field $\kappa=\mathrm{ResidueField}\,A$ has characteristic $q$), and write $F_N=$ `modularFunctionFieldC` $\kappa\,N$ for the field generated over $\kappa$ by the reductions of the $q$-expansions of $j$ and $j_N$. Fix a finite set $W$ of places of $F_N/\kappa$ whose members are exactly the supersingular places `ssPlaces q N` $\kappa$, put $S=$ `nodePairsOfPlaces` $(\mathrm{arithFrobC}\,q\,\kappa\,N)\,W$ for the associated set of node pairs formed from $W$ and the coefficientwise $q$-power Frobenius, and fix modular polynomial data `data` for $q$ (a monic $\Phi\in\mathbb Z[X][Y]$ of degree $\psi(q)$ killing $j_q$) satisfying the Kronecker congruence $\Phi \bmod q=(X^q-Y)(X-Y^q)$, together with integrality `hα`, `hβ` of the two degeneracy maps `heckeAlphaBar`, `heckeBetaBar` from level $N$ to level $Nq$ over $\overline{\mathbb Q}$. Let $P$ be a place-specialization datum for these data with residue map `residue A`, furnishing reductions $\mathrm{red}_1=P.\mathrm{reduceFst}$, $\mathrm{red}_2=P.\mathrm{reduceSnd}$ of places of $\overline{F}_{Nq}=$ `modularFunctionFieldBar` $(N q)$ to places of $F_N$, and let $R$ be a prolongation tuple of $P$ subject to `IsModel` (the two divisor laws and the two cusp laws), the regularity law and the node-value law at $W$, the order law at the places fixed by the geometric Frobenius, and the Gauss jump law. Then for every $\sigma$ in the inertia subgroup of $A$ over $\mathbb Q$, every place $V$ of $\overline{F}_{Nq}$ with neither $P.\mathrm{IsStrictFst}\,V$ nor $P.\mathrm{IsStrictSnd}\,V$ and with $\mathrm{red}_1(V)\in W$, every proof that the displacement divisor $\sigma\cdot(V)-(V)$ (the action being via `arithmeticGalois`) has degree zero, and every degree-zero divisor $D$ on $\overline{F}_{Nq}$ such that each place in the support of $D$ is strict on one of the two sides, such that the gluing datum $P.\mathrm{glueData}\,S\,D=(\mathrm{red}_{1*}(D|_{\text{strict fst}}),\ \mathrm{red}_{2*}(D|_{\text{strict snd}}),\ 0)$ is admissible (both divisors of degree zero and vanishing at the first, respectively second, coordinates of the pairs in $S$), and such that $D$ has the same class in $\mathrm{Pic}^0$ as $\sigma\cdot(V)-(V)$: there exists a family $\chi\colon S\to \mathrm{Additive}\,\kappa^{\times}$ whose image under `GluedPic0.nodeUnit` equals the class of $P.\mathrm{glueData}\,S\,D$ in the glued group $\mathrm{GluedPic0}\,S$.
--
--   This is the specialization step identifying, in the glued Picard group of the two components of the reduction of $X_0(Nq)$ at $q$ glued along the supersingular node pairs, the class coming from an inertial displacement $\sigma V-V$ at an annulus point as a purely node-unit class, the prolongation tuple and its laws being taken as hypotheses and the good admissible representative $D$ being given. It is used in the passage to the toric part, where the pair of degree-zero classes attached to such a representative is shown to vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_gluedMk_eq_nodeUnit_of_isGoodDiv_of_admissible_of_pic0Mk_eq_smul_single_sub_self_of_isModel.lean

import Definitions.Def_ModularCurve_ProlongationTuple_JumpLaw
import Definitions.Def_ValuationSubring_ReduceAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.exists_gluedMk_eq_nodeUnit_of_isGoodDiv_of_admissible_of_pic0Mk_eq_smul_single_sub_self_of_isModel
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
      (hO : R.OrderLawFixed) (hJ : GaussJump.JumpLaw R),
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
          ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V → P.reduceFst V ∈ W →
          ∀ (hdeg : arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
              - Finsupp.single V 1
              ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))
            (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
                (F := ↥(modularFunctionFieldBar (N * q)))))
              (hgood : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
              (hadm : P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
                ∈ GluingData.admissible
                    (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W))
              (hcls : Pic0.mk D
                = Pic0.mk ⟨arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
                    - Finsupp.single V 1, hdeg⟩),
                ∃ χ : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) → Additive (ResidueField A)ˣ,
                  GluedPic0.mk (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                      ⟨P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))), hadm⟩
                    = GluedPic0.nodeUnit (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) χ := by sorry
