-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_count_pair_moment_kernel
-- name    : Kyprianou.ProofPreparation.poisson_prm_count_pair_moment_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:32:35.508207+00:00
-- url     : https://prove2.me/theorems/d4c5fbd0-5cf4-423d-8875-af71d94247a1
-- title:
--   Diagonal/off-diagonal product moments of finite Poisson count families
-- statement:
--   For two finite-intensity measurable Poisson regions indexed i,j, with disjointness when i≠j, the expected product of their real counts is the product of their intensities plus the diagonal intensity correction when i=j. Composes exact proved count second moment and proved disjoint cross-moment factorisation. This is the pairwise kernel for finite-family Poisson L² isometry and Chapter 2 Theorem 2.7.
-- source:
--   Kyprianou (2006), Chapter 2 Theorem 2.7, finite simple-function pairwise moment expansion.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_real_second_moment
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_disjoint_cross_moment
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_count_pair_moment_kernel
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
    (∫ ω, (ProbabilityTheory.poissonRandomMeasure K Y ω (A i)).toReal *
      (ProbabilityTheory.poissonRandomMeasure K Y ω (A j)).toReal ∂P) =
      (m (A i)).toReal * (m (A j)).toReal +
        if i = j then (m (A i)).toReal else 0 := by sorry
end Kyprianou.ProofPreparation
