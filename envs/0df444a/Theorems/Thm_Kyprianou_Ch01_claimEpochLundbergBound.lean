-- Prove2me | Theorems.Thm_Kyprianou_Ch01_claimEpochLundbergBound
-- name    : Kyprianou.Ch01.claimEpochLundbergBound
-- status  : Proved
-- author  : @coqelz
-- created : 2026-11-21T09:20:31.013533+00:00
-- url     : https://prove2.me/theorems/284f15c7-a8e2-4973-87fc-f3f1a703aba6
-- title:
--   Lundberg inequality for the claim-epoch random walk of the Cramér–Lundberg model
-- statement:
--   Let $(\tau_i)_{i\ge 0}$ be i.i.d. exponential interarrival times of rate $\lambda$ and $(Y_i)_{i\ge 0}$ i.i.d. claim sizes with law $F$, all jointly independent on a probability space $(\Omega,\mathcal F,\mathbb P)$ (a compound Poisson driver). For a premium rate $c\in\mathbb R$ put
--   $$Z_i = c\,\tau_i - Y_i,$$
--   the net change of the Cramér–Lundberg surplus between consecutive claim epochs, ending with the $i$-th claim. Let $\nu\ge 0$ satisfy the discrete Lundberg equation
--   $$\mathbb E\big[e^{-\nu Z_0}\big] = 1,$$
--   with $e^{-\nu Z_0}$ integrable. Then for every real initial capital $x$,
--   $$\mathbb P\Big(\exists\, n\ge 0:\ x + \sum_{i=0}^{n} Z_i < 0\Big) \le e^{-\nu x}.$$
--
--   The left-hand side is the probability that the surplus, observed just after its claim epochs, ever drops strictly below zero. Ruin of the continuous-time surplus can happen only at a claim epoch, so this inequality gives Lundberg's exponential bound on the ultimate ruin probability (Kyprianou, Theorem 1.10(i)).
--
--   **Formalization Note.** The binder `arrival` is the interarrival sequence $\tau$ of `IsCompoundPoissonDriver` (its name follows the parent statement), so `arrival i ω` is $\tau_i(\omega)$ and the partial sum $\sum_{i\le n}\tau_i$ is the $n$-th claim epoch.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, §1.3.1 and Theorem 1.10(i) (p. 17); the embedded-random-walk form of Lundberg's inequality, cf. Asmussen & Albrecher (2010), Ruin Probabilities, 2nd ed., Ch. IV (Lundberg's inequality).

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem Kyprianou.Ch01.claimEpochLundbergBound
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (premium : ℝ) (nu : ℝ) (hnu : 0 ≤ nu)
    (hint : Integrable
      (fun ω => Real.exp (-nu * (premium * arrival 0 ω - claims 0 ω))) P)
    (hroot : (∫ ω, Real.exp
      (-nu * (premium * arrival 0 ω - claims 0 ω)) ∂P) = 1)
    (x : ℝ) :
    P {ω | ∃ n : ℕ, x + ∑ i ∈ Finset.range (n + 1),
        (premium * arrival i ω - claims i ω) < 0} ≤
      ENNReal.ofReal (Real.exp (-nu * x)) := by
  sorry
