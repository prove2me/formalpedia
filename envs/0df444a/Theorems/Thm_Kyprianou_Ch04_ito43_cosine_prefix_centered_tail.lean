-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cosine_prefix_centered_tail
-- name    : Kyprianou.Ch04.ito43_cosine_prefix_centered_tail
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T21:44:56.076822+00:00
-- url     : https://prove2.me/theorems/93841bdd-a155-4707-b1b1-e41416846967
-- title:
--   Centred full grid cosine prefixes have small maximal tail
-- statement:
--   Apply independent increments and the Kolmogorov maximal inequality. A bounded nonnegative cosine deficit has variance at most its mean times twice the inverse frequency square.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
open Set

theorem Kyprianou.Ch04.ito43_cosine_prefix_centered_tail  {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (Xleft : NNReal -> Omega -> Real)
    (hLeft : ∀ᵐ omega : Omega ∂P,
      forall t : NNReal, 0 < t ->
        Tendsto (fun s : NNReal => X s omega)
          (nhdsWithin t (Set.Iio t))
          (nhds (Xleft t omega))) :
    ∀ T : NNReal,
    let q : ℕ → ℝ → ℝ := fun m z => (1-Real.cos (((m:ℝ)+1)*z))/((m:ℝ)+1)^2
    let μ : ℕ → ℕ → ℝ := fun m n =>
      ∫ w, q m (X (T/(n:NNReal)) w) ∂P
    let D : ℕ → ℕ → ℕ → Omega → ℝ := fun m n k w =>
      q m (X (T*((k+1:ℕ):NNReal)/(n:NNReal)) w -
        X (T*(k:NNReal)/(n:NNReal)) w) - μ m n
    ∀ e : ℝ, 0 < e → ∀ η : ℝ, 0 < η → ∀ᶠ m : ℕ in atTop,
      ∀ᶠ n : ℕ in atTop,
        (P {w | ∃ j ≤ n, e ≤ |∑ k ∈ Finset.range j, D m n k w|}).toReal ≤ η := by sorry
