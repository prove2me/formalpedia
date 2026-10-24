-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCenterIdeal_pairwise_sup_eq_top
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeal_pairwise_sup_eq_top
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-23T17:53:09.925691+00:00
-- url     : https://prove2.me/theorems/f237d55f-42cd-49ec-bd8c-4bcfabb4e884
-- title:
--   Distinct logarithmic center ideals generate the unit ideal
-- statement:
--   Distinct centers under coordinatewise injectivity have logarithmic center ideals whose supremum is the whole polynomial ring.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeal_pairwise_sup_eq_top
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (e : Fin (m + 1) → Nat) (he : ∀ i, 0 < e i)
    (j k : Fin K) (hjk : j ≠ k) :
    logarithmicCenterIdeal (c j) (fun _ => e 0) e ⊔
      logarithmicCenterIdeal (c k) (fun _ => e 0) e = ⊤ := by sorry
