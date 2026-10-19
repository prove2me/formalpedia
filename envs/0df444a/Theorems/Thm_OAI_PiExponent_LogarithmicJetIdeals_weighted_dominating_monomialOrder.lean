-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_dominating_monomialOrder
-- name    : OAI.PiExponent.LogarithmicJetIdeals.weighted_dominating_monomialOrder
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T23:03:42.596639+00:00
-- url     : https://prove2.me/theorems/826000eb-9483-4543-9bca-6f136f20d676
-- title:
--   Build a monomial order from positive variable weights
-- statement:
--   Given positive weights and pure-power exponents whose weighted degrees strictly exceed the cutoff, construct one monomial order in which every exponent of weighted degree at most the cutoff is smaller than each chosen pure-power exponent.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Complex.Basic

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.weighted_dominating_monomialOrder (m : ℕ) (w : Fin (m + 1) → ℝ) (hw : ∀ i, 0 < w i) (D : ℝ) (N : Fin (m + 1) → ℕ) (hN : ∀ i, D < (N i : ℝ) * w i) : ∃ o : MonomialOrder (Fin (m + 1)), ∀ i b, (∑ j, w j * (b j : ℝ) ≤ D) → o.toSyn b < o.toSyn (Finsupp.single i (N i)) := by sorry
