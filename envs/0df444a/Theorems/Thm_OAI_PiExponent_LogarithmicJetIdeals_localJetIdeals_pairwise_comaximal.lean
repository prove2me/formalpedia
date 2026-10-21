-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_localJetIdeals_pairwise_comaximal
-- name    : OAI.PiExponent.LogarithmicJetIdeals.localJetIdeals_pairwise_comaximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T21:05:19.396348+00:00
-- url     : https://prove2.me/theorems/6320a9da-7753-48b2-98fc-d2ad9fa97a7a
-- title:
--   Distinct local jet ideals are comaximal
-- statement:
--   Under the injectivity hypothesis, any two local jet ideals indexed by distinct indices are comaximal.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.localJetIdeals_pairwise_comaximal
    {m : ℕ} (K : ℕ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ)
    (hc : Function.Injective (fun j : Fin K => fun i : Fin m => (j.val : ℂ) * r i)) :
    ∀ j k : Fin K, j ≠ k →
      localJetIdeal (fun i => (j.val : ℂ) * r i) T e ⊔
        localJetIdeal (fun i => (k.val : ℂ) * r i) T e = ⊤ := by sorry
