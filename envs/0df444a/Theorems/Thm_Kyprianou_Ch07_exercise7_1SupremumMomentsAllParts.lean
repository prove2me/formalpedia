-- Prove2me | Theorems.Thm_Kyprianou_Ch07_exercise7_1SupremumMomentsAllParts
-- name    : Kyprianou.Ch07.exercise7_1SupremumMomentsAllParts
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T15:02:31.508001+00:00
-- url     : https://prove2.me/theorems/bf4ccd89-d98e-42e5-8f29-dfead9759710
-- title:
--   Exercise 7.1: all three supremum moment and truncation results
-- statement:
--   Exercise 7.1, complete all three parts with integer n≥1 and the source condition ∫_(1,∞)xⁿΠ(dx)<∞. (i) For each truncation K>0, construct the genuine Lévy process XK whose jump measure replaces every negative jump of size at least K by a jump of magnitude K, using ΠK(B)=Π(B∩(−K,∞))+1_(−K∈B)Π(−∞,−K), and prove E|XK_t|ⁿ finite for t>0 together with finite moments of all orders for the actual descending ladder height of XK. (ii) With a genuinely independent exponential time e_q of rate q>0, prove E[(sup_{s≤e_q}X_s)^n]<∞. (iii) For n≥2, when X has bounded running supremum almost surely, prove E[(sup_{t≥0}X_t)^(n−1)]<∞. Assumptions tie all auxiliary objects to original X and the same jump measure. Part (iii) now has its own all-orders (k>=2) moment premise and concludes all corresponding (k-1) supremum moments; parts (i)-(ii) retain the fixed n premise. The negative truncation atom correctly includes jumps of size exactly -K, per printed p.206.
-- source:
--   Kyprianou (2006), Exercise 7.1(i)–(iii) and (7.31), printed pp.206–207, original PDF pp.215–216, Windows Ky.pdf sheet 108.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
import Definitions.Def_Kyprianou_Ch06_RunningMaximumAndContact
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
open MeasureTheory Filter Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Exercise 7.1(i)-(iii): the order-n positive jump moment implies
moments of truncated processes and descending ladder heights,
exponentially observed supremum moments, and all-time moments. -/
theorem exercise7_1SupremumMomentsAllParts
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (XK : Real → NNReal → Omega → Real)
    (e : Real → Omega → NNReal)
    (Pi : Measure Real) (b : Real) (sigma2 : NNReal)
    (PiK : Real → Measure Real) (bK : Real → Real)
    (FK : Real → NNReal → MeasurableSpace Omega)
    (Ldown : Real → NNReal → Omega → NNReal)
    (n : Nat) (hn : 1 ≤ n)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet P X b sigma2 Pi)
    (hMoment : (∫⁻ x : Real in Set.Ioi 1,
       ENNReal.ofReal (x ^ n) ∂Pi) < ⊤)
    (hPiK : ∀ K : Real, 0 < K → ∀ B : Set Real, MeasurableSet B →
       PiK K B =
          Pi (B ∩ Set.Ioi (-K)) +
          (if -K ∈ B then Pi (Set.Iic (-K)) else 0))
    (hXK : ∀ K : Real, 0 < K →
       Kyprianou.Ch06.IsRealLevyProcess P (XK K) ∧
       Kyprianou.Ch06.IsLevyKhintchineTriplet
         P (XK K) (bK K) sigma2 (PiK K))
    (hDescLocal : ∀ K : Real, 0 < K →
       Kyprianou.Ch06.IsAdmissibleLocalTimeAtMaximum
         P (FK K) (fun t omega => -XK K t omega) (Ldown K))
    (hE : ∀ q : Real, 0 < q →
       (∀ t : NNReal, P {omega | t < e q omega} =
         ENNReal.ofReal (Real.exp (-q * (t : Real)))) ∧
       (∀ (m : Nat) (times : Fin m → NNReal)
         (A : Fin m → Set Real) (B : Set NNReal),
         (∀ i, MeasurableSet (A i)) → MeasurableSet B →
         P {omega | e q omega ∈ B ∧
           (∀ i : Fin m, X (times i) omega ∈ A i)} =
         P {omega | e q omega ∈ B} *
         P {omega | ∀ i : Fin m, X (times i) omega ∈ A i})) :
    ((∀ K : Real, 0 < K →
       (∀ t : NNReal, 0 < t →
         Integrable (fun omega => (XK K t omega) ^ n) P) ∧
       (∀ t : NNReal, 0 < t → ∀ k : Nat,
         Integrable (fun omega =>
           let tau := Kyprianou.Ch06.inverseLocalTime (Ldown K) t omega
           if tau = ⊤ then (0 : Real)
           else (Kyprianou.Ch06.runningMaximum
             (fun s w => -XK K s w) (tau.untopD 0) omega) ^ k) P)) ∧
     (∀ q : Real, 0 < q →
       Integrable (fun omega =>
         (Kyprianou.Ch06.runningMaximum X (e q omega) omega) ^ n) P) ∧
     ((∀ k : Nat, 2 ≤ k →
         (∫⁻ x : Real in Set.Ioi 1,
           ENNReal.ofReal (x ^ k) ∂Pi) < ⊤) →
       (∀ᵐ omega ∂P,
          ∃ M : Real, ∀ t : NNReal, X t omega ≤ M) →
       ∀ k : Nat, 2 ≤ k →
         Integrable (fun omega =>
           (sSup {y : Real | ∃ t : NNReal, y = X t omega}) ^ (k - 1)) P)) := by
  sorry

end Kyprianou.Ch07
