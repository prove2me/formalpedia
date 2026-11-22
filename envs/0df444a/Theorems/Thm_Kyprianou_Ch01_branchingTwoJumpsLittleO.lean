-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingTwoJumpsLittleO
-- name    : Kyprianou.Ch01.branchingTwoJumpsLittleO
-- status  : Proved
-- author  : @coqelz
-- created : 2026-11-22T19:13:09.436753+00:00
-- url     : https://prove2.me/theorems/d82991e4-a21b-40b7-b7e9-edc934278997
-- title:
--   Two jumps of a Markov branching process in $[0,T]$ have probability $o(T)$
-- statement:
--   Let $(Y_t)_{t\ge 0}$ be a continuous-time Markov branching process on $\mathbb{N}$ under the initial laws $(P_y)_{y\in\mathbb{N}}$, with life rate $\lambda>0$, offspring law $(p_k)$ with $p_1=0$, càdlàg paths, and transition laws whose $Q$-matrix at time $0$ is the branching generator ($q(y,y)=-\lambda y$, $q(y,k)=\lambda y\,p_{k+1-y}$). These are the standing hypotheses of Kyprianou, Chapter 1 §1.3.4.
--
--   For $T\ge 0$ let
--
--   $$D_T=\{\omega : \exists\, 0\le a<b<c\le T,\ Y_a(\omega)\ne Y_b(\omega),\ Y_b(\omega)\ne Y_c(\omega)\},$$
--
--   the event that the path makes at least two jumps during $[0,T]$. The theorem states that for every initial population $z$,
--
--   $$\lim_{T\downarrow 0}\frac{P_z(D_T)}{T}=0 .$$
--
--   This short-time estimate is the probabilistic input to the generator of the forward Lamperti time change $X_t=Y_{\varphi_t}$, where $\varphi_t$ is the right inverse of the occupation clock $J_s=\int_0^s Y_u\,du$.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Chapter 1 §1.3.4, Definition 1.14 and equations (1.17)–(1.18), printed pp. 24–26 (short-time jump estimate underlying the Lamperti generator computation).

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingTwoJumpsLittleO
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
    ∀ z : ℕ,
      Tendsto
        (fun T : ℝ => (P z {ω | ∃ a b c : ℝ≥0, a < b ∧ b < c ∧ (c : ℝ) ≤ T ∧
            Y a ω ≠ Y b ω ∧ Y b ω ≠ Y c ω}).toReal / T)
        (𝓝[>] 0) (𝓝 0) := by sorry
