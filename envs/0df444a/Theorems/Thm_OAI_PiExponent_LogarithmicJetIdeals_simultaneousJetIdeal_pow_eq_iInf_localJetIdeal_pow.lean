-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_simultaneousJetIdeal_pow_eq_iInf_localJetIdeal_pow
-- name    : OAI.PiExponent.LogarithmicJetIdeals.simultaneousJetIdeal_pow_eq_iInf_localJetIdeal_pow
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T22:07:50.272077+00:00
-- url     : https://prove2.me/theorems/08e4441a-6397-4899-b472-1e4d0aad9628
-- title:
--   Powers of simultaneous jet ideals as intersections of local powers
-- statement:
--   When some coordinate of `r` is nonzero and all coordinate exponents are positive, the power of the simultaneous jet ideal equals the infimum of the powers of its local jet ideals.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets

open OAI.PiExponent OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.simultaneousJetIdeal_pow_eq_iInf_localJetIdeal_pow
    {m : ℕ} (K : ℕ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ)
    (hr : ∃ i, r i ≠ 0) (he : ∀ i, 0 < e i)
    (k : ℕ) :
    (simultaneousJetIdeal K r T e) ^ k =
      ⨅ j : Fin K,
        (localJetIdeal (fun i => (j.val : ℂ) * r i) T e) ^ k := by sorry
