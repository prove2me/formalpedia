-- Prove2me | Theorems.Thm_IntConeFPT_sparse_perspective_projection
-- name    : IntConeFPT.sparse_perspective_projection
-- status  : Open
-- author  : @ohnesorgefelix
-- created : 2026-11-25T08:44:38.838886+00:00
-- url     : https://prove2.me/theorems/3ad814c4-8d66-4366-a49c-f82728f09088
-- title:
--   Projecting a sparse generator pattern onto its integer counts
-- statement:
--   Fix a supported representation using at most $s=\tau 2^d$ generators, of positive total count, satisfying the aggregate inequalities with integral right-hand side of magnitude at most $U$. There is an integral system on at most $s$ count variables, with coefficients and right-hand sides bounded by $H=(sk+1)!U^{sk+1}$. The system contains a nonnegative integer vector with the original cost. Every feasible nonnegative integer vector lifts to supported multiplicities of the same linear cost and with total count equal to its coordinate sum. For homogeneous aggregate constraints the projected right-hand side can be zero. Use one count and one scaled continuous block per supported generator, holding its type and integer coordinates fixed, then eliminate the continuous blocks with bounded Farkas multipliers.
-- source:
--   Jansen, Ohnesorge and Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, https://arxiv.org/abs/2609.31328, §3.6, equation (3.4), and Appendix B, proof of Lemma 15. The statement isolates the fixed-pattern perspective and projection step.

import Definitions.Def_IntConeFPT_Formulation

open IntConeFPT

theorem IntConeFPT.sparse_perspective_projection (I : Instance) (hI : I.Valid) (M U : ℕ)
    (hbox : ∀ t, ∀ p ∈ I.P t, InBox M p) (hU : 1 ≤ U) (D : IntDesc I) (hD : D.Describes)
    (hDU : D.BoundedBy M U)
    (μ : Mult I) (hs : I.Supported μ)
    (hcard : ∑ t, (μ t).support.card ≤ I.τ * 2 ^ I.d)
    (hpos : 0 < I.totalCount μ)
    (rhs : Fin D.mW → ℤ) (hrhs : ∀ i, |rhs i| ≤ (U : ℤ))
    (hagg : ∀ i, D.aggLHS (fun t => I.typeAgg μ t) i ≤ rhs i) :
    let s := I.τ * 2 ^ I.d
    let H := (s * I.k + 1).factorial * U ^ (s * I.k + 1)
    ∃ (p m : ℕ) (A : Matrix (Fin m) (Fin p) ℤ) (b : Fin m → ℤ)
      (c : Fin p → ℝ) (z : Fin p → ℕ),
      1 ≤ p ∧ p ≤ s ∧ (∀ i j, |A i j| ≤ (H : ℤ)) ∧ (∀ i, |b i| ≤ (H : ℤ)) ∧
      (rhs = 0 → b = 0) ∧ (∀ i, ∑ j, A i j * (z j : ℤ) ≤ b i) ∧
      (∑ j, (z j : ℝ) * c j) = I.cost μ ∧
      ∀ y : Fin p → ℕ, (∀ i, ∑ j, A i j * (y j : ℤ) ≤ b i) →
        ∃ ν : Mult I, I.Supported ν ∧
          (∀ i, D.aggLHS (fun t => I.typeAgg ν t) i ≤ rhs i) ∧
          I.totalCount ν = ∑ j, y j ∧ I.cost ν = ∑ j, (y j : ℝ) * c j := by sorry
