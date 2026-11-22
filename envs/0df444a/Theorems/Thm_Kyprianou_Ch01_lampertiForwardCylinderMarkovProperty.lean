-- Prove2me | Theorems.Thm_Kyprianou_Ch01_lampertiForwardCylinderMarkovProperty
-- name    : Kyprianou.Ch01.lampertiForwardCylinderMarkovProperty
-- status  : Proved
-- author  : @coqelz
-- created : 2026-11-22T16:30:22.657331+00:00
-- url     : https://prove2.me/theorems/cce417bb-afbb-474d-8988-48188480901a
-- title:
--   Strong Markov property on cylinder events for the forward Lamperti time change
-- statement:
--   Let $Y$ be a continuous-time Markov branching process on $\mathbb{N}$ with holding rate $\lambda > 0$, offspring law $(p_k)_{k \ge 0}$ ($p_1 = 0$), and càdlàg paths under initial laws $(P_y)_{y \in \mathbb{N}}$. Then the forward Lamperti time-changed process $X_t = Y_{\varphi_t}$ satisfies the strong Markov property on cylinder events: for all $u_1, \dots, u_m \le s$, states $v_i$, elapsed time $t \ge 0$ and target state $k$, $P_y(\bigcap_{i=1}^m \{X_{u_i} = v_i\} \cap \{X_{s+t} = k\}) = \sum_{z \in \mathbb{N}} P_y(\bigcap_{i=1}^m \{X_{u_i} = v_i\} \cap \{X_s = z\}) P_z(X_t = k)$.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Chapter 1 §1.3.4, Definition 1.14 and equations (1.17)–(1.18), printed pp. 24–26; sub-lemma of lampertiForwardTimeChangeMarkov.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.lampertiForwardCylinderMarkovProperty
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
    ∀ (y : ℕ) (m : ℕ) (u : Fin m → ℝ≥0) (v : Fin m → ℕ) (s t : ℝ≥0) (k : ℕ),
      (∀ i, u i ≤ s) →
      P y ({ω | ∀ i, branchingToPoisson Y (u i) ω = v i} ∩
          {ω | branchingToPoisson Y (s + t) ω = k}) =
        ∑' z : ℕ, P y ({ω | ∀ i, branchingToPoisson Y (u i) ω = v i} ∩
          {ω | branchingToPoisson Y s ω = z}) *
          P z {ω | branchingToPoisson Y t ω = k} := by
  sorry
