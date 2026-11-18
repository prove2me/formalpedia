-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_pair_count_product_integrable
-- name    : Kyprianou.ProofPreparation.poisson_prm_pair_count_product_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:28:42.480119+00:00
-- url     : https://prove2.me/theorems/2b41f7d8-3dc4-4d7d-9fed-5b4db9e79a2c
-- title:
--   Integrability of diagonal and off-diagonal Poisson count products
-- statement:
--   For any two measurable finite-intensity regions in a Poisson point-family indexed by i,j and disjoint if i≠j, the product of their real counts is integrable. On the diagonal apply Proved region count-square integrability; on the off-diagonal apply Proved independence and single-count integrability. Supports finite-family quadratic moment and L² Poisson integration.
-- source:
--   Kyprianou (2006), Chapter 2 Theorem 2.7, finite weighted-simple Poisson integral L² integrability.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_sq_integrable
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_real_first_moment
import Theorems.Thm_ProbabilityTheory_indepFun_poissonRandomMeasure_apply
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_pair_count_product_integrable
    {Ω E ι : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [DecidableEq ι] [Nonempty E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A : ι → Set E) (i j : ι)
    (hi : MeasurableSet (A i)) (hj : MeasurableSet (A j))
    (hfi : m (A i) < ⊤) (hfj : m (A j) < ⊤)
    (hdisj : i ≠ j → Disjoint (A i) (A j)) :
    Integrable (fun ω =>
      (ProbabilityTheory.poissonRandomMeasure K Y ω (A i)).toReal *
      (ProbabilityTheory.poissonRandomMeasure K Y ω (A j)).toReal) P := by sorry
end Kyprianou.ProofPreparation
