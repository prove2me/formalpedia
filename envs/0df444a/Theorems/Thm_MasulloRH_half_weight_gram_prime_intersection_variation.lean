-- Prove2me | Theorems.Thm_MasulloRH_half_weight_gram_prime_intersection_variation
-- name    : MasulloRH.half_weight_gram_prime_intersection_variation
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T19:37:27.699473+00:00
-- url     : https://prove2.me/theorems/5970d05a-aab9-4c83-9256-24726351a88e
-- title:
--   Sharp signed variation for simultaneous half-weight prime intersection masses
-- statement:
--   Assign each rational prime $p$ the half-weight mass $h_p=p(\log p)^2/(p-1)^2$. On a finite prime set $P$, put $W_P=\sum_{p\in P}h_p$. The target intersection masses on subsets $J\subseteq P$ are $H(\varnothing)=1$, $H(\{p\})=h_p$, and $H(J)=0$ for $|J|\ge2$. Let $w_n$ be any real integrable densities of mass one, with possibly varying reference measures and measurable match events at every prime. Let $C_n(J)$ be the signed mass of simultaneous matches at all primes in $J$. Then
--   $$ |1-W_P|+W_P\;\le\;\int |w_n|+2\sum_{J\subseteq P}|C_n(J)-H(J)|. $$
--   For exact data the left side is the minimum total variation and a finite atomic law attains it. Already $h_2+h_3>37/20$, so an exact normalized signed fit at those two primes costs more than $27/10$ in total variation. If $C_n(J)\to H(J)$ for every fixed nonempty finite $J$, then $\int |w_n|\to\infty$. The result allows arbitrary dependence among the match events. The prescribed numbers are the input for the simultaneous indentation test in the rational principal pole component.
-- source:
--   Masullo, The Music of the Primes, frozen 20 November 2026, §§7.3.2 and 11.3.2. The common-incidence interpretation and half-weight targets are proposed in the mission discussion, comment 44693f8b-68ff-423d-b992-dfe89541d4e1 (Yi). The finite error estimate and pointwise-limit conclusion apply to signed densities on any measured space. The earlier theorem f5007dae-59af-42d8-a692-489a0a965039 treats a different two-prime test at evaluation parameter 1. This theorem verifies the measure and prime-sum obstruction conditional on the stated target masses. Identification of those masses with global Hilbert projection traces is a separate analytic argument.

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
open Finset Filter
open scoped BigOperators Topology Classical
open MeasureTheory

theorem MasulloRH.half_weight_gram_prime_intersection_variation {Ω : Type*} [MeasurableSpace Ω] (μ : ℕ → Measure Ω)
    (w : ℕ → Ω → ℝ) (E : ℕ → Ω → Set Nat.Primes)
    (hw : ∀ n, Integrable (w n) (μ n)) (hn : ∀ n, ∫ x, w n x ∂μ n = 1)
    (hE : ∀ n p, MeasurableSet {x | p ∈ E n x}) :
    let h := fun p : Nat.Primes => (p : ℝ) * (Real.log (p : ℝ))^2 / ((p : ℝ)-1)^2
    let W := fun P : Finset Nat.Primes => ∑ p ∈ P, h p
    let obs := fun n (J : Finset Nat.Primes) =>
      ∫ x, (if (J : Set Nat.Primes) ⊆ E n x then w n x else 0) ∂μ n
    let model := fun (P J : Finset Nat.Primes) => (if J = ∅ then 1 - W P else 0) +
      ∑ p ∈ P, if (J : Set Nat.Primes) ⊆ {p} then h p else 0
    (∀ n P, |1 - W P| + W P ≤ (∫ x, |w n x| ∂μ n) +
      2 * ∑ J ∈ P.powerset, |obs n J - model P J|) ∧
    (37 / 20 < h ⟨2, Nat.prime_two⟩ + h ⟨3, Nat.prime_three⟩) ∧
    (∀ P, ∃ (F : Finset (Option Nat.Primes)) (b : Option Nat.Primes → ℝ)
        (A : Option Nat.Primes → Set Nat.Primes),
      (∑ i ∈ F, b i) = 1 ∧
      (∀ J : Finset Nat.Primes, (∑ i ∈ F, if (J : Set Nat.Primes) ⊆ A i then b i else 0) = model P J) ∧
      (∑ i ∈ F, |b i|) = |1 - W P| + W P) ∧
    ((∀ p, Tendsto (fun n => obs n {p}) atTop (𝓝 (h p))) →
      (∀ J, 2 ≤ J.card → Tendsto (fun n => obs n J) atTop (𝓝 0)) →
      Tendsto (fun n => ∫ x, |w n x| ∂μ n) atTop atTop) := by sorry
