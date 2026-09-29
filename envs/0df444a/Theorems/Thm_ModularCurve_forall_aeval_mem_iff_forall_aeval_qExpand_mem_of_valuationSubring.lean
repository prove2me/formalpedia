-- Prove2me | Theorems.Thm_ModularCurve_forall_aeval_mem_iff_forall_aeval_qExpand_mem_of_valuationSubring
-- name    : ModularCurve.forall_aeval_mem_iff_forall_aeval_qExpand_mem_of_valuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/f6809871-d53b-595b-9e50-104a0c686cd0
-- title:
--   Transfer of the valuation condition from j to j(qτ)
-- statement:
--   Fix a prime $q$ and a field $L$ of characteristic zero, let $K$ be an intermediate field of the extension $L \subseteq L((t))$ of Laurent series, and let $A$ be a discrete valuation domain equipped with an $L$-algebra structure making $L$ its fraction field, with $q \in \mathfrak m_A$. Let $j \in K$ be an element whose image in $L((t))$ is the coefficientwise image along $\mathbb Q \to L$ ([`ModularCurve.coeffEmb`](def/ModularCurve_LaurentCoeff.html#L81)) of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), the Laurent series $t^{-1}$ times the rational-coefficient power series `jNumQ`, and let $j' \in K$ be an element whose image in $L((t))$ is obtained from that of $j$ by [`ModularCurve.qExpand L q`](def/ModularCurve_X0.html#L25), the ring endomorphism of $L((t))$ multiplying all exponents by $q$. Let $V$ be a valuation subring of $K$ such that every element of $A$ maps into $V$ under $A \to L \to K$, and every element of $\mathfrak m_A$ maps into the non-units of $V$. Then the following are equivalent: for every $P \in A[X]$ whose reduction along the residue map of $A$ is non-zero, the value at $j$ of the image of $P$ in $L[X]$ lies in $V$ and so does its inverse; and the same statement with $j$ replaced by $j'$.
--
--   This is the transfer, along the correspondence $j(\tau) \mapsto j(q\tau)$, of the condition that a valuation subring be generic with respect to $j$ (the condition singling out the Gauss point of the $j$-line over the residue field of $A$). It is used in the analysis of branches and level structures on modular curves, in particular by [`ModularCurve.FullLevel.forall_algebraMap_mem_iff_iff_forall_qExpand_mem_iff_of_levelH`](thm.html#ModularCurve.FullLevel.forall_algebraMap_mem_iff_iff_forall_qExpand_mem_iff_of_levelH) and in the computation of level laws at the Igusa branch.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_forall_aeval_mem_iff_forall_aeval_qExpand_mem_of_valuationSubring.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.forall_aeval_mem_iff_forall_aeval_qExpand_mem_of_valuationSubring
    (q : ℕ) [Fact q.Prime]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)
    (j' : ↥K) (hj' : ((j' : LaurentSeries L)) = ModularCurve.qExpand L q ((j : ↥K) : LaurentSeries L))
    (V : ValuationSubring ↥K)
    (hA : ∀ a : A, algebraMap L ↥K (algebraMap A L a) ∈ V)
    (hm : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap L ↥K (algebraMap A L a) ∈ V.nonunits) :
    (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j (P.map (algebraMap A L)) ∈ V ∧ (Polynomial.aeval j (P.map (algebraMap A L)))⁻¹ ∈ V) ↔
      (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j' (P.map (algebraMap A L)) ∈ V ∧ (Polynomial.aeval j' (P.map (algebraMap A L)))⁻¹ ∈ V) := by sorry
