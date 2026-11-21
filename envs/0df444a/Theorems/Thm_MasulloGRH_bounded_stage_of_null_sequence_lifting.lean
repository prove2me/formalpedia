-- Prove2me | Theorems.Thm_MasulloGRH_bounded_stage_of_null_sequence_lifting
-- name    : MasulloGRH.bounded_stage_of_null_sequence_lifting
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-20T23:55:39.848569+00:00
-- url     : https://prove2.me/theorems/2fbcfd0d-43bc-4581-9e88-4067978d35ef
-- title:
--   Lifting null sequences into countably many stages suffices to lift bounded sets
-- statement:
--   Let $E$ be a topological complex vector space and let $j_n:P_n\to E$ be a countable family of injective linear maps from complex topological vector spaces. Assume that every sequence tending to zero in $E$ can be lifted, term by term, to a sequence tending to zero in one $P_n$. Then every bounded subset $B\subset E$ admits a bounded lift: $$\exists n\ \exists A\subseteq P_n\text{ bounded},\qquad B\subseteq j_n(A).$$ This isolates the implication from sequential retractivity to regularity and does not require the stage images to be nested.
-- source:
--   J. Wengenroth, Acyclic inductive spectra of Fréchet spaces, Studia Math. 120 (1996), 247–258, Definition 2.1 and Theorem 2.7, https://doi.org/10.4064/sm-120-3-247-258 . The implication from null-sequence lifting to bounded-set lifting is proved here by a diagonal argument for a general countable family of linear embeddings.

import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Complex.Basic

open Set Filter Topology Bornology
namespace MasulloGRH

theorem bounded_stage_of_null_sequence_lifting (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (P : ℕ → Type*) [∀ n, AddCommGroup (P n)] [∀ n, Module ℂ (P n)]
    [∀ n, TopologicalSpace (P n)] [∀ n, ContinuousSMul ℂ (P n)]
    (j : ∀ n, P n →ₗ[ℂ] E) (hinj : ∀ n, Function.Injective (j n))
    (hseq : ∀ u : ℕ → E, Tendsto u atTop (𝓝 0) →
      ∃ (n : ℕ) (v : ℕ → P n), Tendsto v atTop (𝓝 0) ∧ ∀ k, j n (v k) = u k)
    (B : Set E) (hB : IsVonNBounded ℂ B) :
    ∃ (n : ℕ) (A : Set (P n)), IsVonNBounded ℂ A ∧ B ⊆ j n '' A := by sorry

end MasulloGRH
