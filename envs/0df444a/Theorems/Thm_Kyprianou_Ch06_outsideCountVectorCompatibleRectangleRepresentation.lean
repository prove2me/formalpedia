-- Prove2me | Theorems.Thm_Kyprianou_Ch06_outsideCountVectorCompatibleRectangleRepresentation
-- name    : Kyprianou.Ch06.outsideCountVectorCompatibleRectangleRepresentation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T05:49:58.670215+00:00
-- url     : https://prove2.me/theorems/f7f2f16b-318a-43aa-b778-783fcfcea0ea
-- title:
--   Lemma 6.18 combinatorial helper: finite disjoint mark-time partition of arbitrary count vectors
-- statement:
--   Every finite vector of outside-A Poisson point counts at arbitrary times and overlapping finite-intensity measurable mark sets is almost surely a deterministic function of finitely many count increments on compatible, mutually nonoverlapping mark-time rectangles. The component rectangles have finite intensity, avoid A, and any two are time-separated or have disjoint mark sets. This isolates the genuine finite Boolean-mark and time-interval partition from the Poisson first-arrival independence argument.
-- source:
--   Kyprianou (2006), Lemma 6.18(ii), printed pp.160–161, deterministic finite-partition step in the marked-Poisson proof.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.outsideCountVectorCompatibleRectangleRepresentation
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A) (hFinite : n A < ⊤)
    (m : Nat) (times : Fin m → NNReal) (B : Fin m → Set E)
    (hB : ∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) :
    ∃ (k : Nat) (starts stops : Fin k → NNReal)
      (D : Fin k → Set E),
      (∀ i, starts i ≤ stops i ∧ MeasurableSet (D i) ∧ n (D i) < ⊤) ∧
      (∀ i, Disjoint A (D i)) ∧
      (∀ i j : Fin k, i ≠ j →
        stops i ≤ starts j ∨ stops j ≤ starts i ∨
          Disjoint (D i) (D j)) ∧
      ∃ f : (Fin k → Nat) → Fin m → Nat,
        ∀ᵐ omega ∂P,
          (fun i : Fin m => N omega (times i) (B i)) =
            f (fun i : Fin k =>
              N omega (stops i) (D i) - N omega (starts i) (D i)) := by
  sorry
