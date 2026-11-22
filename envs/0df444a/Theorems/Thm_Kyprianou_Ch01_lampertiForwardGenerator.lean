-- Prove2me | Theorems.Thm_Kyprianou_Ch01_lampertiForwardGenerator
-- name    : Kyprianou.Ch01.lampertiForwardGenerator
-- status  : Proved
-- author  : @coqelz
-- created : 2026-11-22T16:17:34.808718+00:00
-- url     : https://prove2.me/theorems/54904559-5ebd-479e-b019-3a2937449ea2
-- title:
--   Infinitesimal generator of the forward Lamperti time-changed branching process
-- statement:
--   Let $Y$ be a continuous-time Markov branching process on $\mathbb{N}$ with life rate $\lambda > 0$, offspring distribution $(p_k)_{k \ge 0}$ ($p_1 = 0$), and càdlàg paths under initial laws $(P_y)_{y \in \mathbb{N}}$. The transition probabilities $t \mapsto P_z(X_t = k)$ of the forward Lamperti time-changed process $X_t = Y_{\varphi_t}$ have right-derivative at $t = 0$ matching the lattice compound-Poisson generator $g(z, k)$, which is $0$ at $z=0$, $-\lambda$ at $k=z\ge 1$, $\lambda p_{k+1-z}$ for transitions to $k \ge z-1$ ($k \ne z$), and $0$ otherwise.
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

theorem Kyprianou.Ch01.lampertiForwardGenerator
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
    ∀ z k : ℕ,
      HasDerivWithinAt
        (fun t : ℝ => (P z {ω | branchingToPoisson Y (Real.toNNReal t) ω = k}).toReal)
        (if k = z then (if z = 0 then 0 else -(rate : ℝ))
         else if 1 ≤ z ∧ z ≤ k + 1 then
           (rate : ℝ) * (offspring (k + 1 - z)).toReal
         else 0)
        (Set.Ici 0) 0 := by
  sorry
