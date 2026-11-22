-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stoppedCompoundPoissonMarkov
-- name    : Kyprianou.Ch01.stoppedCompoundPoissonMarkov
-- status  : Proved
-- author  : @coqelz
-- created : 2026-11-22T10:14:50.899995+00:00
-- url     : https://prove2.me/theorems/0e97933c-a2d7-4f59-a9c5-782003be5f5f
-- title:
--   Integer compound Poisson process stopped at zero is a bounded-rate Markov chain
-- statement:
--   Let $(\tau_n)$ be i.i.d. $\mathrm{Exp}(\lambda)$ interarrival times and $(\xi_n)$ i.i.d. marks, jointly independent under $Q$. The marks are supported on $\{k-1:k\in\mathbb N\}$ with $Q(\xi=k-1)=p_k$ and $p_1=0$. For $y\in\mathbb N$ let $X^y_t=\lfloor y+\sum_{n:\,T_n\le t}\xi_n\rfloor$, and stop it at its first time in $(-\infty,0]$, i.e. set it to $0$ from that time on. This is Kyprianou's comparison process in (1.17)–(1.18).
--
--   The claim is that this stopped process is a.s. nonnegative and is a time-homogeneous Markov chain with the bounded lattice generator. There is a PMF transition family $K_z(t)$ on $\mathbb N$ satisfying Chapman–Kolmogorov with $K_z(0)=\delta_z$, whose right derivative at $0$ is
--   $$g(z,k)=\begin{cases}0 & z=0,\\ -\lambda & k=z\ge 1,\\ \lambda\,p_{k+1-z} & z\ge 1,\ k\ne z,\ k\ge z-1,\\ 0 & \text{otherwise},\end{cases}$$
--   For every $y$, the following hold:
--   - $X^y_t\ge0$ a.s. for each $t$;
--   - each $(X^y_t)^+$ is a.e.-measurable;
--   - $X^y_0=y$ a.s.;
--   - for all $u_1,\dots,u_m\le s$, $t\ge 0$ and states $v_i,k$,
--   $$Q\big(X^y_{u_i}=v_i\ \forall i,\ X^y_{s+t}=k\big)=\sum_z Q\big(X^y_{u_i}=v_i\ \forall i,\ X^y_s=z\big)K_z(t)(k),$$
--     with states read through $\mathbb Z\to\mathbb N$ truncation.
--
--   This is the Markov property of a compound Poisson process at deterministic times, which comes from the memorylessness of the exponential clocks, together with stopping at the skip-free downward barrier $0$.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Chapter 1 §1.3.4, Definition 1.14 and equations (1.17)–(1.18), printed pp. 24–26; sub-lemma of the forward Lamperti finite-dimensional law target 45b13ab4-970c-4134-a679-c62b276b5f42.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stoppedCompoundPoissonMarkov
    {Ω' : Type*} [MeasurableSpace Ω']
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hRate : 0 < rate)
    (offspring : PMF ℕ) (hNoNullJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω' → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hDriver : IsCompoundPoissonDriver
      arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k) :
    ∃ lawC : PopulationLaws,
      IsPopulationMarkovSemigroup lawC ∧
      (∀ z : ℕ, lawC z 0 = PMF.pure z) ∧
      (∀ z k : ℕ,
        HasDerivWithinAt
          (fun t : ℝ => ((lawC z (Real.toNNReal t)) k).toReal)
          (if k = z then (if z = 0 then 0 else -(rate : ℝ))
           else if 1 ≤ z ∧ z ≤ k + 1 then
             (rate : ℝ) * (offspring (k + 1 - z)).toReal
           else 0)
          (Set.Ici 0) 0) ∧
      ∀ y : ℕ,
        (∀ t : ℝ≥0, ∀ᵐ ω ∂Q,
          0 ≤ stoppedIntegerCompoundPoisson y arrival marks t ω) ∧
        (∀ t : ℝ≥0, AEMeasurable
          (fun ω => (stoppedIntegerCompoundPoisson y arrival marks t ω).toNat) Q) ∧
        Q {ω | (stoppedIntegerCompoundPoisson y arrival marks 0 ω).toNat = y} = 1 ∧
        ∀ (m : ℕ) (u : Fin m → ℝ≥0) (v : Fin m → ℕ) (s t : ℝ≥0) (k : ℕ),
          (∀ i, u i ≤ s) →
          Q ({ω | ∀ i,
                (stoppedIntegerCompoundPoisson y arrival marks (u i) ω).toNat = v i} ∩
              {ω | (stoppedIntegerCompoundPoisson y arrival marks (s + t) ω).toNat = k}) =
            ∑' z : ℕ, Q ({ω | ∀ i,
                (stoppedIntegerCompoundPoisson y arrival marks (u i) ω).toNat = v i} ∩
              {ω | (stoppedIntegerCompoundPoisson y arrival marks s ω).toNat = z}) *
              lawC z t k := by sorry
