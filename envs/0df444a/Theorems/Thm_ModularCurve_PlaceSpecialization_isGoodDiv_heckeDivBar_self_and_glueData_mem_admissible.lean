-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_isGoodDiv_heckeDivBar_self_and_glueData_mem_admissible
-- name    : ModularCurve.PlaceSpecialization.isGoodDiv_heckeDivBar_self_and_glueData_mem_admissible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/525bfa49-6cb3-50fc-9e2f-0ab389a17830
-- title:
--   U_q preserves good divisors and transports their gluing data
-- statement:
--   Fix a natural number $N \neq 0$ and a prime $q$ with $q \nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that $q$ belongs to the non-units of $A$; then the residue field $\kappa = \mathrm{ResidueField}\,A$ has characteristic $q$, and the statement is made with the Hecke-algebra module structures on $\mathrm{JZero}(Nq)$ and $\mathrm{JZero}(N)$ in force. Let $W$ be a finite set of places of the level-$N$ function field $\mathrm{modularFunctionFieldC}\,\kappa\,N$ whose members are exactly the supersingular places `ssPlaces q N (ResidueField A)`, i.e. the rational affine geometric places whose $j$-value lies in `ssJSet q`, and suppose the finite set $S$ of node pairs $\{(w,\ \mathrm{arithFrobC}\cdot w) : w \in W\}$, formed with the coefficientwise $q$-power Frobenius semilinear automorphism $\mathrm{arithFrobC}$, is stable under $\mathrm{arithFrobC}$ in the sense that $(g\cdot s_1, g\cdot s_2) \in S$ for all $s \in S$. Let `data` be a modular polynomial datum for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ vanishing on the pair of $q$-expansions) satisfying the Kronecker congruence $\Phi \equiv (X^q - Y)(X - Y^q) \pmod q$, let $h\alpha, h\beta$ assert integrality of the two degeneracy inclusions from level $N$ to level $Nq$, and let $P$ be a place specialisation of level $N$ at $A$ relative to these data, providing a map `P.sp` on places and a homomorphism on $\mathrm{Pic}^0$ compatible with the orders of $j$ and $j_N$. Then, given integrality hypotheses $h\alpha', h\beta'$ for the two degeneracy inclusions from level $Nq$ to level $Nq^2$ and the existence of principal divisors at level $Nq^2$, every divisor $D$ on $\mathrm{modularFunctionFieldBar}(Nq)$ which is good for $P$ (each place in its support is strict of the first kind, $\mathrm{Frob}(\mathrm{reduceFst}\,W) = \mathrm{reduceSnd}\,W$ with $\mathrm{Frob}^2(\mathrm{reduceFst}\,W) \neq \mathrm{reduceFst}\,W$, or strict of the second kind, the symmetric condition) and whose gluing datum $\mathrm{glue}(D) = (E_1, E_2, 0)$, with $E_1$ the pushforward under `P.reduceFst` of the strict-first part of $D$ and $E_2$ the pushforward under `P.reduceSnd` of the strict-second part, is admissible (both $E_1, E_2$ of degree zero and vanishing at the respective components of all pairs in $S$), satisfies: the Hecke transform $\mathrm{heckeDivBar}\,h\alpha'\,h\beta'\,D = \alpha_*\beta^* D$ is again good for $P$, its gluing datum is again admissible, and that gluing datum equals $(F^*E_1 + (q-1)E_2,\ \varphi_* E_2,\ 0)$, where $F^*$ is `frobeniusPullbackGeomLevel` (each place replaced by a chosen Frobenius preimage, with coefficient multiplied by $q$) and $\varphi_*$ is `frobeniusPushforwardGeomLevel` (pushforward along the geometric Frobenius on places).
--
--   This is the divisor-level description of the action of the Hecke correspondence $U_q$ on the semistable reduction of $X_0(Nq)$ at the prime $q$, where the special fibre is two copies of the level-$N$ curve glued along supersingular points: on admissible gluing data the correspondence acts by the matrix with entries $F^*$, $q-1$ and $\varphi_*$. It is used by [`ModularCurve.PlaceSpecialization.exists_good_admissible_rep_heckeDivBar_self_good_admissible`](thm.html#ModularCurve.PlaceSpecialization.exists_good_admissible_rep_heckeDivBar_self_good_admissible), which supplies good representatives with admissible gluing data for the level-lowering argument at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_isGoodDiv_heckeDivBar_self_and_glueData_mem_admissible.lean

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
set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.isGoodDiv_heckeDivBar_self_and_glueData_mem_admissible (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
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
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ),
        (∀ (hα' : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * q) q)
            (hβ' : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * q) q)
            [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q * q))]
            (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
            P.IsGoodDiv D →
            P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) D
                ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) →
              P.IsGoodDiv (heckeDivBar hα' hβ' D) ∧
              P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (heckeDivBar hα' hβ' D)
                  ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) ∧
              P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (heckeDivBar hα' hβ' D)
                = (frobeniusPullbackGeomLevel (ResidueField A) N data hKr
                      (Finsupp.mapDomain P.reduceFst (P.fstDiv D))
                    + ((q : ℤ) - 1) • Finsupp.mapDomain P.reduceSnd (P.sndDiv D),
                   frobeniusPushforwardGeomLevel (ResidueField A) N data hKr
                      (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)),
                   0)) := by sorry
