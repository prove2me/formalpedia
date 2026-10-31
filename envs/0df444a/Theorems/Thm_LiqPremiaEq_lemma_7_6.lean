-- Prove2me | Theorems.Thm_LiqPremiaEq_lemma_7_6
-- name    : LiqPremiaEq.lemma_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:02:05.390994+00:00
-- url     : https://prove2.me/theorems/58d426a6-236e-4185-90f1-8d5d8ec0eac2
-- title:
--   Lemma 7.6 — $\tau\mapsto\|Y(\tau)\|_{op}$ is increasing when $A(\tau)\succeq0$
-- statement:
--   Let $A$ be a continuous $M\times M$ matrix function with $A(\tau)$ positive semidefinite ($b^\top A(\tau)b\ge0$, no symmetry) for every $\tau$, and let $Y$ solve $Y'(\tau)=A(\tau)Y(\tau)$, $Y(0)=I_M$ (7.3). Then
--
--   $$\tau\mapsto\|Y(\tau)\|_{op}$$
--
--   is increasing (non-decreasing).
--
--   Applied to $\Psi_F(\cdot;\tau)$, this gives the contraction bound of Corollary 7.8.
--
--   Differences from the source:
--   - generalization: A, Y on ℝ₊ = [0, ∞) → any solution on any initial interval [0, T′), T′ ∈ ℝ; reason: the proof never uses maximality or the whole half-line; taking T′ = T_max (resp. every T′ = τ + 1) gives the printed statement
--   - generalization: Y the solution of (7.3) as in Lemma 7.5, where A(0) = 0 is assumed → no condition on A(0); reason: A(0) = 0 is a hypothesis of Lemma 7.5, not of (7.3), and the proof of Lemma 7.6 does not use it; the printed case satisfies the Lean hypotheses
--   - reading: positive (semi)definite → IsPSDQuad A: bᵀAb ≥ 0 for all b (IsPDQuad: bᵀAb > 0 for b ≠ 0), no symmetry required; reason: footnotes 10 (p.8) and 19 (p.14): the matrices are not symmetric and the notions are meant without symmetry
--   - encoding: “increasing” → MonotoneOn (weakly increasing); reason: the proof shows ‖Y(τ)‖op ≥ ‖Y(r)‖op for τ ≥ r
--   - encoding: “the unique solution” Y of (7.3) → Y any solution of (7.3) on [0, T′) (IsLinMatODESol); reason: (7.3) has a unique solution
--   - encoding: matrix ODEs on an interval → every entry has the stated derivative within the interval at each of its points (one-sided at the endpoints); reason: entrywise differentiability is differentiability of a matrix function on a finite-dimensional space
--   - encoding: Frobenius norm ‖·‖ (p.3) and operator norm ‖·‖op (Definition 7.2) → explicit functions frobVec, frob and opNorm (the ℓ² operator norm of Matrix.toEuclideanLin A); reason: avoids Mathlib’s default sup norm; same values
-- source:
--   Muhle-Karbe–Shi–Yang, An Equilibrium Model for the Cross-Section of Liquidity Premia, arXiv:2011.13625v1, Lemma 7.6, p.18

import Mathlib
import Definitions.Def_LiqPremiaEq_opNorm
import Definitions.Def_LiqPremiaEq_IsPSDQuad
import Definitions.Def_LiqPremiaEq_IsLinMatODESol

open Matrix

namespace LiqPremiaEq

/-- **Lemma 7.6.** Let `Y` solve the linear matrix ODE `Y′(τ) = A(τ)Y(τ)`, `Y(0) = I` (7.3). If
`τ ↦ A(τ)` is continuous and `A(τ)` is positive semidefinite for every `τ`, then
`τ ↦ ‖Y(τ)‖op` is (weakly) increasing.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Lemma 7.6, p.18.

**Formalization Note** Stated on every initial interval `[0, T′)` instead of `ℝ₊`; `A(0) = 0`
(a hypothesis of Lemma 7.5, not of (7.3)) is not assumed. `‖·‖op` is the `ℓ²` operator norm
(Definition 7.2). Positive semidefinite means `bᵀAb ≥ 0` without symmetry. -/
theorem lemma_7_6 {m : Type*} [Fintype m] [DecidableEq m] (T' : ℝ) (A Y : ℝ → Matrix m m ℝ)
    (hA : ContinuousOn A (Set.Ico 0 T')) (hY : IsLinMatODESol (Set.Ico 0 T') A Y)
    (hpsd : ∀ τ ∈ Set.Ico 0 T', IsPSDQuad (A τ)) :
    MonotoneOn (fun τ => opNorm (Y τ)) (Set.Ico 0 T') := by sorry

end LiqPremiaEq
