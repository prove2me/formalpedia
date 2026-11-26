-- Prove2me | Theorems.Thm_HMBinPacking_lenstra_residue_optimization
-- name    : HMBinPacking.lenstra_residue_optimization
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:00:11.52548+00:00
-- url     : https://prove2.me/theorems/49444684-6e48-5a5f-be60-91b1cd5cce25
-- title:
--   Lemma 7, equivalence and attainment of the residue integer program and polytope optimization
-- statement:
--   In every nonempty bin configuration residue class, optimization of an arbitrary rational objective over its convex hull equals optimization over the bounded integer variables parametrizing the class. One feasible nonnegative integer vector simultaneously realizes both maxima; the integer feasible set is finite and contains zero.
-- source:
--   Koana, Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2, Proof of Lemma 7, p.5. The arithmetic or geometric subclaim in the proof of Lemma 7.

import Definitions.Def_HMBinPacking_ILP
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
open Finset HMBinPacking
open scoped Pointwise

namespace HMBinPacking

theorem lenstra_residue_optimization (I : Instance) (r : Fin I.d → Fin I.d)
    (hr : ∑ i, I.s i * (r i : ℕ) ≤ I.B) :
    (fun i => ((r i : ℕ) : ℤ)) ∈ Sr I r ∧
    {y' : Fin I.d → ℕ | ∑ i, I.s i * ((r i : ℕ) + I.d * y' i) ≤ I.B}.Finite ∧
    (∀ y : Fin I.d → ℕ, (∑ i, I.s i * ((r i : ℕ) + I.d * y i) ≤ I.B) →
      (fun i => (((r i : ℕ) + I.d * y i : ℕ) : ℝ)) ∈ Pr I r) ∧
    ∀ u : Fin I.d → ℚ, ∃ y : Fin I.d → ℕ,
        ∑ i, I.s i * ((r i : ℕ) + I.d * y i) ≤ I.B ∧
        (fun i => (((r i : ℕ) + I.d * y i : ℕ) : ℝ)) ∈ Pr I r ∧
        IsGreatest ((fun x : Fin I.d → ℝ => ∑ i, (u i : ℝ) * x i) '' Pr I r)
          (∑ i, (u i : ℝ) * (((r i : ℕ) + I.d * y i : ℕ) : ℝ)) ∧
        IsGreatest ((fun y' : Fin I.d → ℕ => ∑ i, (u i : ℝ) * (((r i : ℕ) + I.d * y' i : ℕ) : ℝ)) ''
            {y' | ∑ i, I.s i * ((r i : ℕ) + I.d * y' i) ≤ I.B})
          (∑ i, (u i : ℝ) * (((r i : ℕ) + I.d * y i : ℕ) : ℝ)) := by sorry

end HMBinPacking
