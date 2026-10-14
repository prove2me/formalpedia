-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_distinct_local_jet_ideals_isCoprime
-- name    : OAI.PiExponent.LogarithmicJetIdeals.distinct_local_jet_ideals_isCoprime
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-13T22:57:08.208989+00:00
-- url     : https://prove2.me/theorems/044f26e6-fa7e-415f-9986-1b8c3cd81e3b
-- title:
--   Distinct centers give comaximal local jet ideals
-- statement:
--   Injectivity of the center map ensures that any distinct pair of indices gives comaximal local jet ideals. A coordinate where the centers differ gives translated generators differing by a nonzero scalar; if an exponent is zero, the corresponding ideal is already the unit ideal.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.distinct_local_jet_ideals_isCoprime
    {m : ℕ} (K : ℕ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ)
    (hc : Function.Injective (fun j : Fin K => fun i : Fin m => (j.val : ℂ) * r i)) :
    ∀ j k : Fin K, j ≠ k →
      IsCoprime
        (localJetIdeal (fun i => (j.val : ℂ) * r i) T e)
        (localJetIdeal (fun i => (k.val : ℂ) * r i) T e) := by sorry
