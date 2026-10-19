-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_localJetIdeal_pairwise_isCoprime
-- name    : OAI.PiExponent.LogarithmicJetIdeals.localJetIdeal_pairwise_isCoprime
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T17:21:59.570196+00:00
-- url     : https://prove2.me/theorems/31ead997-e784-49a0-a647-af5b50190925
-- title:
--   Rectangular logarithmic jet ideals at distinct centers are comaximal
-- statement:
--   At injectively indexed centers, the existing rectangular local ideals with positive coordinate exponents are pairwise comaximal. A separating coordinate gives two generators differing by a nonzero constant; pass to their powers and then to the larger local ideals. Pairwise conditions are vacuous for at most one center, including the injective m=0 case.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets

open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.localJetIdeal_pairwise_isCoprime
    {m K : ℕ} (c : Fin K → Fin m → ℂ) (T : Fin m → ℕ)
    (b : Fin (m + 1) → ℕ) (hb : ∀ i, 0 < b i)
    (hc : Function.Injective c) :
    Pairwise (fun j l : Fin K =>
      IsCoprime (localJetIdeal (c j) T b) (localJetIdeal (c l) T b)) := by sorry
