-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stoppedCompoundPoissonCylinderMarkov
-- name    : Kyprianou.Ch01.stoppedCompoundPoissonCylinderMarkov
-- status  : Proved
-- author  : @coqelz
-- created : 2026-11-22T11:21:46.399309+00:00
-- url     : https://prove2.me/theorems/47a25e4f-99ac-45d9-bbe4-ff6eb1407762
-- title:
--   Stopped integer compound Poisson process: Markov property along cylinder events
-- statement:
--   Let $(\tau_n)$ be i.i.d. $\mathrm{Exp}(\lambda)$ interarrival times ($\lambda>0$) and $(\xi_n)$ i.i.d. marks, jointly independent under $Q$. The marks are almost surely in $\{k-1:k\in\mathbb N\}$. For $y\in\mathbb N$ let $C_t=\sum_{n:\,T_n\le t}\xi_n$ with arrival times $T_n=\tau_0+\dots+\tau_n$. Let $X^y$ be the integer path $\lfloor y+C_t\rfloor$, stopped (set to $0$) from its first time in $(-\infty,0]$. This is Kyprianou's comparison process for the forward Lamperti transform (1.17)–(1.18).
--
--   For every $y$:
--
--   - $X^y_t\ge0$ almost surely for each $t$;
--   - each $(X^y_t)^+$ is a.e.-measurable;
--   - $X^y_0=y$ almost surely;
--   - the **Markov property along cylinder events** holds with transition probabilities $Q(X^z_t=k)$: for all times $u_1,\dots,u_m\le s$, states $v_i$, $t\ge0$ and $k$,
--   $$Q\big(X^y_{u_i}=v_i\ \forall i,\ X^y_{s+t}=k\big)=\sum_{z\in\mathbb N} Q\big(X^y_{u_i}=v_i\ \forall i,\ X^y_s=z\big)\,Q\big(X^z_t=k\big).$$
--
--   States are read through the truncation $\mathbb Z\to\mathbb N$. The content is the regeneration of the compound Poisson process at the deterministic time $s$: by memorylessness of the exponential clocks, the post-$s$ increments form a fresh compound Poisson process independent of the past. Combine this with the facts that the process stopped at $0$ stays at $0$, and that whether it has stopped by time $s$ is decided by the path up to $s$.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Chapter 1 §1.3.4, equations (1.17)–(1.18), printed pp. 24–26; sub-lemma of Kyprianou.Ch01.stoppedCompoundPoissonMarkov (0e97933c-a2d7-4f59-a9c5-782003be5f5f).

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stoppedCompoundPoissonCylinderMarkov
    {Ω' : Type*} [MeasurableSpace Ω']
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hRate : 0 < rate)
    (arrival marks : ℕ → Ω' → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hDriver : IsCompoundPoissonDriver
      arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1) :
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
            Q {ω | (stoppedIntegerCompoundPoisson z arrival marks t ω).toNat = k} := by sorry
