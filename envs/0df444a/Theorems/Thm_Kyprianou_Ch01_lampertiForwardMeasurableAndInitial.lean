-- Prove2me | Theorems.Thm_Kyprianou_Ch01_lampertiForwardMeasurableAndInitial
-- name    : Kyprianou.Ch01.lampertiForwardMeasurableAndInitial
-- status  : Proved
-- author  : @coqelz
-- created : 2026-11-22T16:30:13.194536+00:00
-- url     : https://prove2.me/theorems/0cc18226-d6aa-42e3-b07c-9e8c07f6fee8
-- title:
--   Initial value and path measurability of the forward Lamperti time change
-- statement:
--   Let $Y$ be a continuous-time Markov branching process on $\mathbb{N}$ with holding rate $\lambda > 0$, offspring law $(p_k)_{k \ge 0}$ ($p_1 = 0$), and càdlàg paths under initial laws $(P_y)_{y \in \mathbb{N}}$. Then for each initial state $y \in \mathbb{N}$, the forward Lamperti time-changed process $X_t = Y_{\varphi_t}$ is almost everywhere measurable at each time $t \ge 0$, and preserves the initial state $X_0 = y$ almost surely under $P_y$.
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

theorem Kyprianou.Ch01.lampertiForwardMeasurableAndInitial
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
    ∀ y : ℕ,
      (∀ t : ℝ≥0, AEMeasurable (fun ω => branchingToPoisson Y t ω) (P y)) ∧
      P y {ω | branchingToPoisson Y 0 ω = y} = 1 := by
  sorry
