-- Prove2me | Theorems.Thm_OAI_PiExponent_WeightedDivision_choose_monic_blocks
-- name    : OAI.PiExponent.WeightedDivision.choose_monic_blocks
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:26:22.825596+00:00
-- url     : https://prove2.me/theorems/3007f9cd-c627-4840-ad78-db20ab13a037
-- title:
--   Choose a prescribed number of monic blocks
-- statement:
--   From a total of at least $s$ whole coordinate blocks, choose multiplicities totaling exactly $s$ that fit within each coordinate exponent.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

theorem OAI.PiExponent.WeightedDivision.choose_monic_blocks
    {ι : Type*} [Fintype ι]
    (b : ι → ℕ) (hb : ∀ i, 0 < b i)
    (u : ι →₀ ℕ) (s : ℕ)
    (hu : s ≤ ∑ i, u i / b i) :
    ∃ k : ι → ℕ, (∀ i, k i * b i ≤ u i) ∧ (∑ i, k i = s) := by sorry
