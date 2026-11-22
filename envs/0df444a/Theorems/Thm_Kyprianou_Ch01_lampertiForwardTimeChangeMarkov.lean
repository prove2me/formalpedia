-- Prove2me | Theorems.Thm_Kyprianou_Ch01_lampertiForwardTimeChangeMarkov
-- name    : Kyprianou.Ch01.lampertiForwardTimeChangeMarkov
-- status  : Proved
-- author  : @coqelz
-- created : 2026-11-22T10:14:52.239145+00:00
-- url     : https://prove2.me/theorems/04482571-1fb4-469d-bf4b-7d2226982059
-- title:
--   Forward Lamperti time change of a Markov branching process is a bounded-rate Markov chain
-- statement:
--   Let $Y$ be a continuous-time Markov branching process on $\mathbb N$ with life rate $\lambda>0$ and offspring law $(p_k)$ with $p_1=0$, under the initial-state laws $P_y$, with càdlàg paths, and with no moment assumption on the offspring law. Write $J_t=\int_0^t Y_s\,ds$, let $\varphi_t=\inf\{s: J_s>t\}$ be the right inverse of this occupation clock, and let $X_t=Y_{\varphi_t}$ (with $X_t=0$ when $\varphi_t=\infty$). This is the forward Lamperti transform of Kyprianou (1.17).
--
--   The claim is that $X$ is a time-homogeneous Markov chain on $\mathbb N$ with **bounded** jump rates. Concretely, there is a family of transition laws $K_z(t)$ (PMFs on $\mathbb N$) such that:
--
--   - $K$ satisfies Chapman–Kolmogorov, $K_z(s+t)=\sum_n K_z(s)(n)\,K_n(t)$, and $K_z(0)=\delta_z$;
--   - its right derivative at $t=0$ is the lattice compound-Poisson generator
--   $$g(z,k)=\begin{cases}0 & z=0,\\ -\lambda & k=z\ge 1,\\ \lambda\,p_{k+1-z} & z\ge 1,\ k\ne z,\ k\ge z-1,\\ 0 & \text{otherwise},\end{cases}$$
--     so that from $z\ge1$ the chain jumps at rate $\lambda$ to $z+j-1$ with probability $p_j$, and $0$ is absorbing;
--   - under each $P_y$, every $X_t$ is a.e.-measurable, $X_0=y$ almost surely, and for all finitely many times $u_1,\dots,u_m\le s$, states $v_i$, $t\ge0$ and $k$,
--   $$P_y\big(X_{u_i}=v_i\ \forall i,\ X_{s+t}=k\big)=\sum_{z} P_y\big(X_{u_i}=v_i\ \forall i,\ X_s=z\big)\,K_z(t)(k).$$
--
--   This is the probabilistic heart of the forward Lamperti correspondence. The holding rate $\lambda y$ of $Y$ in state $y$ is slowed by the factor $y$ of the clock to the constant rate $\lambda$. It requires the strong Markov property of $Y$ at the stopping times $\varphi_t$.
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

theorem Kyprianou.Ch01.lampertiForwardTimeChangeMarkov
    {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℕ)
    (P : ℕ → Measure Ω) (law : PopulationLaws)
    (rate : ℝ≥0) (hRate : 0 < rate)
    (offspring : PMF ℕ) (hNoNullJumps : offspring 1 = 0)
    (hBranching : HasBranchingProperty law)
    (hMarkov : IsPopulationMarkovPath Y P law)
    (hSemigroup : IsPopulationMarkovSemigroup law)
    (hGenerator : IsBranchingRateGenerator law rate offspring)
    (hInitial : ∀ y : ℕ, P y {ω | Y 0 ω = y} = 1)
    (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ y : ℕ, ∀ᵐ ω ∂P y,
      IsCadlag (fun t : ℝ≥0 => Y t ω)) :
    ∃ lawX : PopulationLaws,
      IsPopulationMarkovSemigroup lawX ∧
      (∀ z : ℕ, lawX z 0 = PMF.pure z) ∧
      (∀ z k : ℕ,
        HasDerivWithinAt
          (fun t : ℝ => ((lawX z (Real.toNNReal t)) k).toReal)
          (if k = z then (if z = 0 then 0 else -(rate : ℝ))
           else if 1 ≤ z ∧ z ≤ k + 1 then
             (rate : ℝ) * (offspring (k + 1 - z)).toReal
           else 0)
          (Set.Ici 0) 0) ∧
      ∀ y : ℕ,
        (∀ t : ℝ≥0, AEMeasurable (fun ω => branchingToPoisson Y t ω) (P y)) ∧
        P y {ω | branchingToPoisson Y 0 ω = y} = 1 ∧
        ∀ (m : ℕ) (u : Fin m → ℝ≥0) (v : Fin m → ℕ) (s t : ℝ≥0) (k : ℕ),
          (∀ i, u i ≤ s) →
          P y ({ω | ∀ i, branchingToPoisson Y (u i) ω = v i} ∩
              {ω | branchingToPoisson Y (s + t) ω = k}) =
            ∑' z : ℕ, P y ({ω | ∀ i, branchingToPoisson Y (u i) ω = v i} ∩
              {ω | branchingToPoisson Y s ω = z}) * lawX z t k := by sorry
