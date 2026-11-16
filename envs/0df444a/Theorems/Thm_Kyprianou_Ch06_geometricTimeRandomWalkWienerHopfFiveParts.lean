-- Prove2me | Theorems.Thm_Kyprianou_Ch06_geometricTimeRandomWalkWienerHopfFiveParts
-- name    : Kyprianou.Ch06.geometricTimeRandomWalkWienerHopfFiveParts
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T22:17:15.808072+00:00
-- url     : https://prove2.me/theorems/f5c6a812-f9c3-4c8a-a0e1-10c3630142b6
-- title:
--   Exercise 6.9: full five-part random-walk Wiener–Hopf factorisation
-- statement:
--   For a random walk with iid non-atomic two-sided increments, starting at S₀=0, sampled at an independent geometric Γ_p with p∈(0,1), prove all five parts: (i) the complete Frullani/Spitzer transform of (Γ,SΓ) and infinite divisibility; (ii) geometric compound representation in full law of (G,S_G) from strict ladder-time/height pairs conditioned on N≤Γ and its infinite-divisibility implication; (iii) independence of pre/postmaximum pairs and dual law of the postmaximum pair with the last-minimum pair; (iv) the positive-side Spitzer factor; and (v) both the first-ladder transform ratio and Baxter's identity. Include sample-time zero in extrema, and handle the s=1 Baxter singularity by a separate limiting argument. Part (i), including infinite divisibility at geometric time, now quantifies over general iid random-walk increments. Atomlessness and two-sided signs are assumptions only for the stronger clauses (ii)-(v).
-- source:
--   Kyprianou (2006), Exercise 6.9(i)–(v), printed pp. 177–178; physical two-up PDF p. 94.

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Exercise 6.9: all five parts of the geometric-time random-walk
Wiener-Hopf factorisation. Maxima and minima are taken over time
indices INCLUDING zero; Γ=0 is permitted. Under the atomless increment
law the time of a finite maximum is almost surely unique. -/
theorem geometricTimeRandomWalkWienerHopfFiveParts
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (S : Nat → Omega → Real) (Gamma : Omega → Nat)
    (p : Real) (hp : 0 < p ∧ p < 1)
    (hZero : ∀ᵐ omega ∂P, S 0 omega = 0)
    (hIncrements : ∀ (k : Nat) (A : Fin k → Set Real),
      (∀ i, MeasurableSet (A i)) →
      P {omega | ∀ i : Fin k,
        S ((i : Nat) + 1) omega - S (i : Nat) omega ∈ A i} =
        ∏ i : Fin k, P {omega | S 1 omega ∈ A i})
    (hGeo : ∀ n : Nat,
      P {omega | Gamma omega = n} =
        ENNReal.ofReal (p * (1 - p) ^ n))
    (hGeoIndependent : ∀ (n k : Nat)
      (A : Fin k → Set Real),
      (∀ i, MeasurableSet (A i)) →
      P {omega | Gamma omega = n ∧
        (∀ i : Fin k, S ((i : Nat) + 1) omega -
          S (i : Nat) omega ∈ A i)} =
        P {omega | Gamma omega = n} *
        P {omega | ∀ i : Fin k,
          S ((i : Nat) + 1) omega -
            S (i : Nat) omega ∈ A i}) :
    let q : Real := 1 - p
    let high : Omega → Real := fun omega =>
      sSup ((fun n : Nat => S n omega) ''
        {n : Nat | n ≤ Gamma omega})
    let low : Omega → Real := fun omega =>
      sInf ((fun n : Nat => S n omega) ''
        {n : Nat | n ≤ Gamma omega})
    let G : Omega → Nat := fun omega =>
      sSup {n : Nat | n ≤ Gamma omega ∧
        S n omega = high omega}
    let D : Omega → Nat := fun omega =>
      sSup {n : Nat | n ≤ Gamma omega ∧
        S n omega = low omega}
    let N : Omega → WithTop Nat := fun omega =>
      sInf ((fun n : Nat => (n : WithTop Nat)) ''
        {n : Nat | 0 < n ∧ 0 < S n omega})
    let rho : ENNReal := P {omega |
      (Gamma omega : WithTop Nat) < N omega}
    -- (i) Spitzer's geometric-time transform and infinite divisibility
    (∀ (s theta : Real), 0 < s → s ≤ 1 →
      (∫ omega,
        (↑(s ^ Gamma omega) : Complex) *
          Complex.exp (Complex.I *
            (↑(theta * S (Gamma omega) omega) : Complex)) ∂P) =
      Complex.exp (-
        ∑' n : Nat,
          ((↑(q ^ (n + 1) / (n + 1 : Real)) : Complex) *
            (1 - (↑(s ^ (n + 1)) : Complex) *
              (∫ omega,
                Complex.exp (Complex.I *
                  (↑(theta * S (n + 1) omega) : Complex))
                ∂P))))) ∧
    (∀ m : Nat, 0 < m →
      ∃ nu : Measure (Nat × Real),
        IsProbabilityMeasure nu ∧
        ∀ (s theta : Real), 0 < s → s ≤ 1 →
          (∫ omega,
            (↑(s ^ Gamma omega) : Complex) *
              Complex.exp (Complex.I *
                (↑(theta * S (Gamma omega) omega) : Complex)) ∂P) =
          (∫ z : Nat × Real,
            (↑(s ^ z.1) : Complex) *
              Complex.exp (Complex.I *
                (↑(theta * z.2) : Complex)) ∂nu) ^ m) ∧
    -- (ii)-(v) need stronger hypotheses; (i) above holds for
    -- arbitrary iid increments, including atomic or one-sided laws.
    ((∀ x : Real, P {omega | S 1 omega = x} = 0) →
     (0 < P {omega | S 1 omega < 0} ∧
      0 < P {omega | 0 < S 1 omega}) →
    ((0 < rho ∧ rho < 1 ∧
      ∃ Q : Measure (Nat × (Nat → Nat × Real)),
        IsProbabilityMeasure Q ∧
        (∀ k : Nat,
          Q {z | z.1 = k} = rho * (1 - rho) ^ k) ∧
        (∀ (i : Nat) (A : Set (Nat × Real)),
          MeasurableSet A →
          Q {z | z.2 i ∈ A} =
            P {omega |
              N omega ≠ ⊤ ∧
              (N omega).untopD 0 ≤ Gamma omega ∧
              ((N omega).untopD 0,
                S ((N omega).untopD 0) omega) ∈ A} /
              (1 - rho)) ∧
        (∀ (k : Nat) (A : Fin k → Set (Nat × Real)),
          (∀ i, MeasurableSet (A i)) →
          Q {z | ∀ i : Fin k, z.2 i ∈ A i} =
            ∏ i : Fin k, Q {z | z.2 i ∈ A i}) ∧
        (∀ (k m : Nat) (A : Fin m → Set (Nat × Real)),
          (∀ i, MeasurableSet (A i)) →
          Q {z | z.1 = k ∧
            (∀ i : Fin m, z.2 i ∈ A i)} =
            Q {z | z.1 = k} *
            Q {z | ∀ i : Fin m, z.2 i ∈ A i}) ∧
        Measure.map (fun omega => (G omega, S (G omega) omega)) P =
          Measure.map
            (fun z : Nat × (Nat → Nat × Real) =>
              ∑ i ∈ Finset.range z.1, z.2 i) Q) ∧
    -- (iii) independence of the premaximum and postmaximum pieces,
    -- and duality to the random-walk last minimum
    (∀ A B : Set (Nat × Real),
      MeasurableSet A → MeasurableSet B →
      P {omega | (G omega, S (G omega) omega) ∈ A ∧
        (Gamma omega - G omega,
          S (Gamma omega) omega - S (G omega) omega) ∈ B} =
        P {omega | (G omega, S (G omega) omega) ∈ A} *
        P {omega | (Gamma omega - G omega,
          S (Gamma omega) omega - S (G omega) omega) ∈ B}) ∧
    (∀ A : Set (Nat × Real), MeasurableSet A →
      P {omega | (Gamma omega - G omega,
        S (Gamma omega) omega - S (G omega) omega) ∈ A} =
      P {omega | (D omega, S (D omega) omega) ∈ A}) ∧
    -- (iv) Spitzer's positive-side factor, including s=1
    (∀ (s theta : Real), 0 < s → s ≤ 1 →
      (∫ omega,
        (↑(s ^ G omega) : Complex) *
          Complex.exp (Complex.I *
            (↑(theta * S (G omega) omega) : Complex)) ∂P) =
      Complex.exp (-
        ∑' n : Nat,
          ((↑(q ^ (n + 1) / (n + 1 : Real)) : Complex) *
            (↑(P {omega | 0 < S (n + 1) omega}).toReal : Complex) -
          (↑(q ^ (n + 1) * s ^ (n + 1) /
            (n + 1 : Real)) : Complex) *
            (∫ omega,
              if 0 < S (n + 1) omega then
                Complex.exp (Complex.I *
                  (↑(theta * S (n + 1) omega) : Complex))
              else (0 : Complex) ∂P)))) ∧
    -- (v) first-ladder transform ratio and Baxter's identity
    (∀ (s theta : Real), 0 < s → s < 1 →
      (∫ omega,
        (↑(s ^ G omega) : Complex) *
          Complex.exp (Complex.I *
            (↑(theta * S (G omega) omega) : Complex)) ∂P) =
      (↑rho.toReal : Complex) /
        (1 - ∫ omega,
          if N omega = ⊤ then (0 : Complex)
          else (↑((q * s) ^ (N omega).untopD 0) : Complex) *
            Complex.exp (Complex.I *
              (↑(theta * S ((N omega).untopD 0) omega) : Complex))
          ∂P)) ∧
    (∀ (s theta : Real), 0 < s → s < 1 →
      (1 : Complex) /
        (1 - ∫ omega,
          if N omega = ⊤ then (0 : Complex)
          else (↑(s ^ (N omega).untopD 0) : Complex) *
            Complex.exp (Complex.I *
              (↑(theta * S ((N omega).untopD 0) omega) : Complex))
          ∂P) =
      Complex.exp (
        ∑' n : Nat,
          (↑(s ^ (n + 1) / (n + 1 : Real)) : Complex) *
            (∫ omega,
              if 0 < S (n + 1) omega then
                Complex.exp (Complex.I *
                  (↑(theta * S (n + 1) omega) : Complex))
              else (0 : Complex) ∂P))))) := by
  sorry

end Kyprianou.Ch06
