-- Prove2me | Theorems.Thm_Kyprianou_Ch03_finiteCylinderOfOrderedGridLawsV1
-- name    : Kyprianou.Ch03.finiteCylinderOfOrderedGridLawsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:22:50.904325+00:00
-- url     : https://prove2.me/theorems/1088e47a-f954-4cf5-9b03-b4bfe35b5c82
-- title:
--   Finite cylinder masses from zero-based ordered grid laws
-- statement:
--   Cover the prescribed finite set with a zero-based monotone grid. Choose an index for each prescribed coordinate; the event of satisfying all coordinate restrictions is a finite intersection of measurable coordinate events on the grid vector. Pull back using the two equal grid laws.
-- source:
--   Kyprianou (2006), Chapter 3 Lemma 3.4; parent rawReversalFiniteCylinderV1 8ac9ed28-eeeb-4802-8031-7ce3fe9b88b5.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch03.finiteCylinderOfOrderedGridLawsV1
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    (t : NNReal) (F G : NNReal → Omega → Real)
    (hF : ∀ s, AEMeasurable (F s) P)
    (hG : ∀ s, AEMeasurable (G s) P)
    (hLaw : ∀ (n : Nat) (q : Fin (n + 1) → NNReal),
      Monotone q → q 0 = 0 → (∀ i, q i ≤ t) →
      P.map (fun ω : Omega => fun i => F (q i) ω) =
      P.map (fun ω : Omega => fun i => G (q i) ω))
    (J : Finset {s : NNReal // s ≤ t})
    (B : {s : NNReal // s ≤ t} → Set Real)
    (hB : ∀ i ∈ J, MeasurableSet (B i)) :
    P ((fun ω : Omega => fun s : {s : NNReal // s ≤ t} => F s ω) ⁻¹'
      Set.pi (J : Set {s : NNReal // s ≤ t}) B) =
    P ((fun ω : Omega => fun s : {s : NNReal // s ≤ t} => G s ω) ⁻¹'
      Set.pi (J : Set {s : NNReal // s ≤ t}) B) := by sorry
