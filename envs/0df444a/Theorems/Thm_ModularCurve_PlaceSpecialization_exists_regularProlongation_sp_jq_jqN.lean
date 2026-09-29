-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_regularProlongation_sp_jq_jqN
-- name    : ModularCurve.PlaceSpecialization.exists_regularProlongation_sp_jq_jqN
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/4fd2aee2-fff5-5a44-a66c-a87193bb2724
-- title:
--   Regular prolongation at level N reducing j and j_N
-- statement:
--   Let $N$ be nonzero, let $q$ be a prime not dividing $N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, meaning that the image of $q$ is a non-unit of $A$; consequently the residue field $k_A = \mathrm{ResidueField}\,A$ has characteristic $q$. Let `data` consist of a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ in $Y$ annihilating the pair $(j, j_q)$ of $q$-expansions, let `hKr` assert the Kronecker congruence $\Phi \equiv (X^q - Y)(X - Y^q) \pmod q$, and let `hα`, `hβ` assert that the two base-changed degeneracy maps $\bar\alpha, \bar\beta$ from the level-$N$ to the level-$Nq$ function field over $\overline{\mathbb{Q}}$ are integral ring homomorphisms. Let $P$ be a place specialization of these data with residue map $A \to k_A$, and let $R$ be a prolongation tuple for $P$ which is in model form (the two divisor laws and the two cusp laws hold) and whose order law at Frobenius-fixed affine geometric places holds. Then there exists a regular prolongation $R_1$ of $A$ on the level-$N$ function field $\mathrm{modularFunctionFieldBar}\,N$ over $\overline{\mathbb{Q}}$ with values in $\mathrm{modularFunctionFieldC}\,k_A\,N$ — that is, a valuation subring of the former together with a surjective homomorphism onto the latter with kernel its maximal ideal, restricting to $A$ and to the residue map of $A$, and satisfying the scaling condition — such that: for every $f$ in the integers of $R_1$ with nonzero residue and every divisor $D$ with $D(V) = \mathrm{ord}_V(f)$ at all places $V$, the pushforward of $D$ along $P.\mathrm{sp}$ satisfies $(P.\mathrm{sp})_*D(Q) = \mathrm{ord}_Q(R_1.\mathrm{residue}\,f)$ at every place $Q$; the coefficientwise image of $j$ lies in the integers of $R_1$ and has residue $\mathrm{jqModC}\,k_A$; and the coefficientwise image of the $N$-fold $q$-expansion of $j$ lies in the integers of $R_1$ and has residue $\mathrm{jqNModC}\,k_A\,N$.
--
--   This is the existence of a constant reduction datum at level $N$, in the style of Igusa's theorem on the Kroneckerian model, whose place map is the given specialization $P.\mathrm{sp}$ and whose residue map sends the two modular generators $j$, $j_N$ to their characteristic-$q$ counterparts, the last two clauses pinning down the reduction up to no automorphism of the special fibre. It is used in the comparison of Hecke divisors with divisors on the special fibre and in the construction of the glued specialization matrices at the nodes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_regularProlongation_sp_jq_jqN.lean

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.exists_regularProlongation_sp_jq_jqN (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := heckeModuleBar (N * q)
    letI := heckeModuleBar N
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel) (hO : R.OrderLawFixed),
      ∃ R₁ : RegularProlongation A (modularFunctionFieldBar N)
          (modularFunctionFieldC (ResidueField A) N),
        (∀ f : R₁.integers, R₁.residue f ≠ 0 →
          ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
            (∀ V, D V = V.ord (f : modularFunctionFieldBar N)) →
          ∀ Q, Finsupp.mapDomain P.sp D Q = Q.ord (R₁.residue f))
        ∧ (∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
            ∈ R₁.integers,
          R₁.residue ⟨_, h⟩
            = ⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩)
        ∧ ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full N (dvd_refl N))⟩ : modularFunctionFieldBar N)
            ∈ R₁.integers,
          R₁.residue ⟨_, h⟩
            = ⟨jqNModC (ResidueField A) N, jqNModC_mem (ResidueField A) N⟩ := by sorry
