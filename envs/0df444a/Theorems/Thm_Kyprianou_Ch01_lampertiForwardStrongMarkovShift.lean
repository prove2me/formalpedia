-- Prove2me | Theorems.Thm_Kyprianou_Ch01_lampertiForwardStrongMarkovShift
-- name    : Kyprianou.Ch01.lampertiForwardStrongMarkovShift
-- status  : Proved
-- author  : @coqelz
-- created : 2026-11-22T18:50:36.615571+00:00
-- url     : https://prove2.me/theorems/6d55bd4d-8e27-4fb3-bda5-eef4f1109123
-- title:
--   Strong Markov property at the Lamperti inverse clock
-- statement:
--   Let $(Y_t)_{t \ge 0}$ be a continuous-time Markov branching process on $\mathbb N = \{0,1,2,\dots\}$, realised on a measurable space $\Omega$ together with laws $(P_y)_{y \in \mathbb N}$, where $P_y$ is the law started from $y$ individuals. Assume:
--
--   - each $Y_t$ is measurable;
--   - $P_y(Y_0 = y) = 1$;
--   - the paths are càdlàg $P_y$-almost surely;
--   - the transition laws $p_t(y,\cdot)$ form a Markov semigroup that has the branching property, the Markov property holds with respect to the natural filtration of $Y$, and the generator is that of a branching process with life rate $\lambda > 0$ and offspring law $(p_k)$ with $p_1 = 0$.
--
--   Define the occupation clock, its right-continuous inverse, and the forward Lamperti time change by
--   $$
--   J_r = \int_0^r Y_u \, du, \qquad \varphi_s = \inf\{ r \ge 0 : J_r > s \}, \qquad X_s = Y_{\varphi_s},
--   $$
--   with $X_s = 0$ when $\varphi_s = \infty$. When $\varphi_s < \infty$, let $X'$ be the forward Lamperti time change of the path restarted at $\varphi_s$, that is, of $r \mapsto Y_{\varphi_s + r}$.
--
--   **Theorem.** Let $y, k \in \mathbb N$ and $z \ge 1$. Let $0 \le u_1, \dots, u_m \le s$, let $v_1, \dots, v_m \in \mathbb N$, and let $t \ge 0$. Then
--   $$
--   P_y\big( X_{u_i} = v_i \ (1 \le i \le m),\ X_s = z,\ X'_t = k \big)
--   = P_y\big( X_{u_i} = v_i \ (1 \le i \le m),\ X_s = z \big)\, P_z( X_t = k ).
--   $$
--
--   On the event $\{X_s = z\}$ with $z \ge 1$, the time $\varphi_s$ is finite and $Y_{\varphi_s} = z$. The theorem says that, conditionally on the time-changed past up to time $s$ and on $X_s = z$, the time change of the restarted path has the same one-dimensional law as $X$ under $P_z$. This is the strong Markov property of $Y$ at the stopping time $\varphi_s$, read through the Lamperti transform. It is the key step in showing that the forward Lamperti time change of a continuous-time branching process is a Markov process, namely a compound Poisson process stopped on hitting $0$.
--
--   **Formalization Note.** $X$ is `branchingToPoisson Y`. The restarted path is written as `fun r ω => Y (sInf {r' | s < branchingOccupation Y r' ω} + r) ω`, where the infimum equals $\varphi_s$ on $\{X_s = z\}$. Probabilities of events are measures of the corresponding sets under `P y`.
-- source:
--   Kyprianou, Fluctuations of Lévy Processes with Applications, Ch. 1 (Lamperti transform for continuous-time branching processes)

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.lampertiForwardStrongMarkovShift
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
    ∀ (y : ℕ) (m : ℕ) (u : Fin m → ℝ≥0) (v : Fin m → ℕ) (s t : ℝ≥0) (z k : ℕ),
      (∀ i, u i ≤ s) → 0 < z →
      P y ({ω | ∀ i, branchingToPoisson Y (u i) ω = v i} ∩
          {ω | branchingToPoisson Y s ω = z} ∩
          {ω | branchingToPoisson
              (fun r ω' => Y (sInf {r' : ℝ≥0 | (s : ℝ) < branchingOccupation Y r' ω'} + r) ω')
              t ω = k}) =
        P y ({ω | ∀ i, branchingToPoisson Y (u i) ω = v i} ∩
          {ω | branchingToPoisson Y s ω = z}) *
          P z {ω | branchingToPoisson Y t ω = k} := by
  sorry
