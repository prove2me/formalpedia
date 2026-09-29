-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_rep_forall_exists_ord_sub_pos_residue_notMem_of_isModel_of_regularityLaw_of_orderLawFixed_of_ssPlaces
-- name    : ModularCurve.PlaceSpecialization.exists_rep_forall_exists_ord_sub_pos_residue_notMem_of_isModel_of_regularityLaw_of_orderLawFixed_of_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/d5d87f44-3c5c-53a3-b8ed-66f27be6c6ce
-- title:
--   Moving lemma: representatives with j-residues avoiding S
-- statement:
--   Let $N \ge 1$ and let $q$ be a prime not dividing $N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that $q$ belongs to the nonunits of $A$; consequently the residue field $k = \mathrm{ResidueField}\,A$ has characteristic $q$. Assume given: a finite set $W$ of places of $\mathrm{modularFunctionFieldC}\,k\,N$ over $k$ whose members are exactly the supersingular places, i.e. the places $w$ that are rational, affine geometric (both $\mathrm{jGeomGen}$ and $\mathrm{jNGeomGen}$ lie in the valuation subring of $w$) and whose value at $\mathrm{jGeomGen}$ lies in $\mathrm{ssJSet}\,q\,k$, the set of $j \in k$ such that every elliptic curve over $k$ with invariant $j$ has no nonzero point killed by $q$; a modular polynomial datum $\mathrm{data}$ of level $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$) satisfying the Kronecker congruence $\Phi \bmod q = (X'^q - X)(X' - X^q)$; integrality of the two degeneracy maps $\overline{\alpha}, \overline{\beta}$ from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$; a place specialisation $P$ for $(A, q, N, \mathrm{data})$ with target $k$ and reduction the residue map of $A$; and a prolongation tuple $R$ for $P$ satisfying $R.\mathrm{IsModel}$ (the two divisor laws and the two cusp laws), the regularity law at $W$, and the order law at Frobenius-fixed affine places. Then for every finite $S \subseteq k$ with no element of $S$ in $\mathrm{ssJSet}\,q\,k$ and every class $x$ in $\mathrm{JZero}(Nq) = \mathrm{Pic}^0$ of $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb{Q}}$, there is a degree-zero divisor $E$ with $\mathrm{Pic0.mk}\,E = x$ such that every place $V$ in the support of $E$ admits $a \in A$ with $V.\mathrm{ord}(j - a) > 0$, where $j$ is the coefficientwise image of the $q$-expansion $\mathrm{jq}$ inside $\mathrm{modularFunctionFieldBar}(Nq)$, and with the residue of $a$ in $k$ outside $S$.
--
--   This is the moving lemma for divisor classes on the two-branch special fibre of $X_0(Nq)$: every degree-zero class is represented by a divisor supported at points whose $j$-invariants specialise to values outside a prescribed finite set of non-supersingular residues. It is the form of the moving lemma in which the regularity law is imposed exactly at the supersingular places, and it feeds the construction of representatives with prescribed reduction behaviour used in the character-group analysis of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_rep_forall_exists_ord_sub_pos_residue_notMem_of_isModel_of_regularityLaw_of_orderLawFixed_of_ssPlaces.lean

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.exists_rep_forall_exists_ord_sub_pos_residue_notMem_of_isModel_of_regularityLaw_of_orderLawFixed_of_ssPlaces
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (_ : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : ProlongationTuple P),
      R.IsModel → R.RegularityLaw W → R.OrderLawFixed →
      ∀ (S : Finset (ResidueField A)) (_ : ∀ s ∈ S, s ∉ ssJSet q (ResidueField A))
        (x : JZero (N * q)),
        ∃ E : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
          Pic0.mk E = x ∧
            ∀ V ∈ (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
              ∃ a : A,
                0 < V.ord
                    (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                          (modularFunctionField_le_full (N * q) (jq_mem (N * q)))⟩
                      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
                          (a : AlgebraicClosure ℚ)) ∧
                  IsLocalRing.residue A a ∉ S := by sorry
