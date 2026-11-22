-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stoppedCompoundPoissonGenerator
-- name    : Kyprianou.Ch01.stoppedCompoundPoissonGenerator
-- status  : Proved
-- author  : @coqelz
-- created : 2026-11-22T11:21:46.054703+00:00
-- url     : https://prove2.me/theorems/1b531d74-db9e-4cc9-98ad-f050baeebaa7
-- title:
--   Stopped integer compound Poisson process: transition probabilities have the lattice generator at time 0
-- statement:
--   Let $(\tau_n)$ be i.i.d. $\mathrm{Exp}(\lambda)$ interarrival times ($\lambda>0$) and $(\xi_n)$ i.i.d. marks, jointly independent under $Q$. The marks are almost surely in $\{k-1:k\in\mathbb N\}$. For $y\in\mathbb N$ let $C_t=\sum_{n:\,T_n\le t}\xi_n$ with arrival times $T_n=\tau_0+\dots+\tau_n$. Let $X^y$ be the integer path $\lfloor y+C_t\rfloor$, stopped (set to $0$) from its first time in $(-\infty,0]$. This is Kyprianou's comparison process for the forward Lamperti transform (1.17)–(1.18). Suppose further that $Q(\xi=k-1)=p_k$ for an offspring law $(p_k)$ with $p_1=0$.
--
--   Then for all $z,k\in\mathbb N$, the map $t\mapsto Q\big((X^z_t)^+=k\big)$ has right derivative at $t=0$ equal to
--   $$g(z,k)=\begin{cases}0 & z=0,\\ -\lambda & k=z\ge 1,\\ \lambda\,p_{k+1-z} & z\ge 1,\ k\ne z,\ k\ge z-1,\\ 0 & \text{otherwise}.\end{cases}$$
--
--   This is a first-jump computation. Up to $o(t)$, the process either has no jump by time $t$ (probability $e^{-\lambda t}$), or exactly one jump of size $j-1$ (probability $\lambda t\,p_j+o(t)$, landing at $z+j-1$, absorbed at $0$ if this is $\le 0$). Two or more jumps have probability $O(t^2)$. The state $0$ is absorbing.
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

theorem Kyprianou.Ch01.stoppedCompoundPoissonGenerator
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
    ∀ z k : ℕ,
      HasDerivWithinAt
        (fun t : ℝ => (Q {ω |
          (stoppedIntegerCompoundPoisson z arrival marks (Real.toNNReal t) ω).toNat = k}).toReal)
        (if k = z then (if z = 0 then 0 else -(rate : ℝ))
         else if 1 ≤ z ∧ z ≤ k + 1 then
           (rate : ℝ) * (offspring (k + 1 - z)).toReal
         else 0)
        (Set.Ici 0) 0 := by sorry
