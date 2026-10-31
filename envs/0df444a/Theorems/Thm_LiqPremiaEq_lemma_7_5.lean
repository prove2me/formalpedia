-- Prove2me | Theorems.Thm_LiqPremiaEq_lemma_7_5
-- name    : LiqPremiaEq.lemma_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:02:13.778392+00:00
-- url     : https://prove2.me/theorems/081bf4f7-ca76-4fb4-ac67-62d338feb7b7
-- title:
--   Lemma 7.5 — if $Y''=BY$ with $B\succeq0$, then $A\succeq0$ for $Y'=AY$, $A(0)=0$
-- statement:
--   Let $A$ be a continuous $M\times M$ matrix function with $A(0)=0$, and let $Y$ solve
--
--   $$Y'(\tau)=A(\tau)Y(\tau),\qquad Y(0)=I_M.\qquad(7.3)$$
--
--   Suppose that $Y''(\tau)=B(\tau)Y(\tau)$ where $B(\tau)$ is positive semidefinite ($b^\top B(\tau)b\ge0$, no symmetry) for all $\tau$. Then $A(\tau)$ is positive semidefinite for all $\tau$.
--
--   The lemma turns a second-order condition on a fundamental matrix into positivity of its generator; it is the step that shows $F\succeq0$ in Corollary 7.7.
--
--   Differences from the source:
--   - generalization: A, Y, B on ℝ₊ = [0, ∞) → any solution on any initial interval [0, T′), T′ ∈ ℝ; reason: the proof never uses maximality or the whole half-line; taking T′ = T_max (resp. every T′ = τ + 1) gives the printed statement
--   - reading: positive (semi)definite → IsPSDQuad A: bᵀAb ≥ 0 for all b (IsPDQuad: bᵀAb > 0 for b ≠ 0), no symmetry required; reason: footnotes 10 (p.8) and 19 (p.14): the matrices are not symmetric and the notions are meant without symmetry
--   - encoding: “the unique solution” Y of (7.3) and “Y″(τ) = B(τ)Y(τ)” → Y any solution of (7.3) on [0, T′) (IsLinMatODESol), and τ ↦ A(τ)Y(τ) (= Y′) has derivative B(τ)Y(τ) within [0, T′); reason: (7.3) has a unique solution, and Y″ is the derivative of Y′ = AY
--   - encoding: matrix ODEs on an interval → every entry has the stated derivative within the interval at each of its points (one-sided at the endpoints); reason: entrywise differentiability is differentiability of a matrix function on a finite-dimensional space
--   - encoding: ℝ^{M×M} → Matrix m m ℝ over an arbitrary finite index type m; reason: the same statement for every dimension
-- source:
--   Muhle-Karbe–Shi–Yang, An Equilibrium Model for the Cross-Section of Liquidity Premia, arXiv:2011.13625v1, Lemma 7.5, pp.17–18

import Mathlib
import Definitions.Def_LiqPremiaEq_IsPSDQuad
import Definitions.Def_LiqPremiaEq_IsLinMatODESol

open Matrix

namespace LiqPremiaEq

/-- **Lemma 7.5.** Let `A` be continuous with `A(0) = 0` and let `Y` solve the linear matrix ODE
`Y′(τ) = A(τ)Y(τ)`, `Y(0) = I` (7.3). Suppose `Y″(τ) = B(τ)Y(τ)` with `B(τ)` positive
semidefinite for all `τ`. Then `A(τ)` is positive semidefinite for all `τ`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Lemma 7.5, pp.17–18.

**Formalization Note** Stated on every initial interval `[0, T′)` instead of `ℝ₊` (the case
`ℝ₊` follows by taking `T′ = τ + 1`). `Y″ = BY` is the statement that the derivative of
`Y′ = AY` is `BY`, all derivatives within `[0, T′)`. Positive semidefinite means `bᵀAb ≥ 0`
without symmetry. -/
theorem lemma_7_5 {m : Type*} [Fintype m] [DecidableEq m] (T' : ℝ)
    (A B Y : ℝ → Matrix m m ℝ) (hA : ContinuousOn A (Set.Ico 0 T')) (hA0 : A 0 = 0)
    (hY : IsLinMatODESol (Set.Ico 0 T') A Y)
    (hY2 : ∀ τ ∈ Set.Ico 0 T',
      HasMatDerivWithinAt (fun x => A x * Y x) (B τ * Y τ) (Set.Ico 0 T') τ)
    (hB : ∀ τ ∈ Set.Ico 0 T', IsPSDQuad (B τ)) :
    ∀ τ ∈ Set.Ico 0 T', IsPSDQuad (A τ) := by sorry

end LiqPremiaEq
