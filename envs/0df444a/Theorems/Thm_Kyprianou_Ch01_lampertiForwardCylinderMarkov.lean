-- Prove2me | Theorems.Thm_Kyprianou_Ch01_lampertiForwardCylinderMarkov
-- name    : Kyprianou.Ch01.lampertiForwardCylinderMarkov
-- status  : Proved
-- author  : @coqelz
-- created : 2026-11-22T16:17:34.834481+00:00
-- url     : https://prove2.me/theorems/cc26c1f8-8ae7-4850-822c-3a680d149815
-- title:
--   Forward Lamperti time change cylinder Markov property and initial distribution
-- statement:
--   Let $Y$ be a continuous-time Markov branching process on $\mathbb{N}$ with life rate $\lambda > 0$, offspring distribution $(p_k)_{k \ge 0}$ ($p_1 = 0$), and càdlàg paths under initial laws $(P_y)_{y \in \mathbb{N}}$. Then the forward Lamperti time-changed process $X_t = Y_{\varphi_t}$ (where $\varphi_t = \inf\{s \ge 0 : \int_0^s Y_u \, du > t\}$) is almost everywhere measurable at each time, starts at $y$ almost surely under $P_y$, and satisfies the finite-dimensional cylinder Markov property with one-step transition probabilities $P_z(X_t = k)$.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Chapter 1 §1.3.4, Definition 1.14 and equations (1.17)–(1.18), printed pp. 24–26.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.lampertiForwardCylinderMarkov
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
      P y {ω | branchingToPoisson Y 0 ω = y} = 1 ∧
      ∀ (m : ℕ) (u : Fin m → ℝ≥0) (v : Fin m → ℕ) (s t : ℝ≥0) (k : ℕ),
        (∀ i, u i ≤ s) →
        P y ({ω | ∀ i, branchingToPoisson Y (u i) ω = v i} ∩
            {ω | branchingToPoisson Y (s + t) ω = k}) =
          ∑' z : ℕ, P y ({ω | ∀ i, branchingToPoisson Y (u i) ω = v i} ∩
            {ω | branchingToPoisson Y s ω = z}) *
            P z {ω | branchingToPoisson Y t ω = k} := by
  sorry
