-- Prove2me | Theorems.Thm_HaahQSP_Decomp_theorem_2
-- name    : HaahQSP.Decomp.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:53.224975+00:00
-- url     : https://prove2.me/theorems/5bf821af-8c6c-4eab-9e60-5d5c2faa16ec
-- title:
--   Theorem 2: unique product decomposition of SU(2) valued Laurent polynomials
-- statement:
--   For each $n\ge0$, every ordered product of $n$ primitive matrices associated with rank one orthogonal projectors belongs to $\mathcal E_n$. Conversely, every $F(t)=\sum_{j=-n}^{n}C_jt^j\in\mathcal E_n$ of degree $n$ has a unique factorization
--
--   $$
--   F(t)=E_0E_{P_1}(t)\cdots E_{P_n}(t),\qquad E_0\in SU(2),
--   $$
--
--   where each $P_j$ is a rank one orthogonal projector. For $n>0$, every such factorization has final projector
--
--   $$
--   P_n=\frac{C_n^\dagger C_n}{\operatorname{Tr}(C_n^\dagger C_n)}.
--   $$
--
--   This characterizes the $SU(2)$ valued Laurent polynomials produced by exactly $n$ primitive factors. The formula also asserts that the denominator is nonzero under the stated hypotheses.
--
--   **Formalization Note** Products are ordered with $P_1$ leftmost and are equal for every nonzero complex $t$. The projector formula is stated only when a last factor exists, and does not assume $C_n\ne0$ separately.
-- source:
--   J. Haah, Product Decomposition of Periodic Functions in Quantum Signal Processing, arXiv:1806.10236v4 (2020), p. 4, Theorem 2

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Int.Interval
import Definitions.Def_HaahQSP_Decomp_Setting

namespace HaahQSP.Decomp

open scoped Matrix

theorem theorem_2 (n : ℕ) :
    (∀ Ps : Fin n → Mat2, (∀ j, IsRankOneProj (Ps j)) →
      ∃ C : ℤ → Mat2, ESet n C ∧
        ∀ t : ℂ, t ≠ 0 → eval n C t = prodPrim n Ps t) ∧
    (∀ C : ℤ → Mat2, ESet n C → HasDegree n C →
      ∃! E : Mat2 × (Fin n → Mat2),
        E.1 ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
        (∀ j, IsRankOneProj (E.2 j)) ∧
        ∀ t : ℂ, t ≠ 0 → eval n C t = E.1 * prodPrim n E.2 t) ∧
    (∀ (hn : 0 < n) (C : ℤ → Mat2) (E0 : Mat2) (Ps : Fin n → Mat2),
      ESet n C → HasDegree n C →
      E0 ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ →
      (∀ j, IsRankOneProj (Ps j)) →
      (∀ t : ℂ, t ≠ 0 → eval n C t = E0 * prodPrim n Ps t) →
      Ps ⟨n - 1, Nat.sub_lt hn (by decide)⟩ =
        (Matrix.trace ((C (n : ℤ))ᴴ * C (n : ℤ)))⁻¹ •
          ((C (n : ℤ))ᴴ * C (n : ℤ))) := by sorry

end HaahQSP.Decomp
