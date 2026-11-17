-- Prove2me | Theorems.Thm_Kyprianou_Ch07_exercise7_2StrongLawAllParts
-- name    : Kyprianou.Ch07.exercise7_2StrongLawAllParts
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T14:53:58.131642+00:00
-- url     : https://prove2.me/theorems/1c79cede-86f1-4d46-b811-93526a74814d
-- title:
--   Exercise 7.2: all four strong-law conclusions for Lévy processes
-- statement:
--   Exercise 7.2 in all four parts. For a Lévy process with E|X₁| finite, let Y_n=sup_{t∈[n,n+1]}|X_t−X_n|. Part (i) proves E Y_n finite for each n. Part (ii) proves Y_n/n→0 almost surely using the strong law. Part (iii) proves X_t/t→E X₁ almost surely over continuous time. Part (iv), with separate extended-mean premise E X₁=+∞ and finite negative mean part, proves X_t/t→+∞ almost surely. The finite-mean assumption does not constrain the separate infinite-mean case.
-- source:
--   Kyprianou (2006), Exercise 7.2(i)–(iv), printed p.207; original single-page PDF p.216; Windows Ky.pdf sheet 109.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch07_UnitTimeOscillationObservables
import Definitions.Def_Kyprianou_Ch07_LevyMeanAndTailTests
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Exercise 7.2(i)–(iv): integrable unit-block oscillations,
negligible unit-block growth, the finite-mean strong law,
and the positive-infinite-mean strong law. -/
theorem exercise7_2StrongLawAllParts
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X) :
    ((Integrable (fun omega => |X 1 omega|) P →
      ((∀ n : Nat, Integrable (maximalUnitIncrement X n) P) ∧
       (∀ᵐ omega ∂P,
         Tendsto (fun n : Nat =>
           maximalUnitIncrement X n omega / (n : Real))
           atTop (nhds (0 : Real))) ∧
       (∀ᵐ omega ∂P,
         Tendsto (fun t : NNReal => X t omega / (t : Real))
           atTop (nhds (∫ omega, X 1 omega ∂P))))) ∧
     (positiveMeanPart P X = ⊤ ∧ negativeMeanPart P X < ⊤ →
       (∀ᵐ omega ∂P,
         Tendsto (fun t : NNReal => X t omega / (t : Real))
           atTop atTop))) := by
  sorry

end Kyprianou.Ch07
