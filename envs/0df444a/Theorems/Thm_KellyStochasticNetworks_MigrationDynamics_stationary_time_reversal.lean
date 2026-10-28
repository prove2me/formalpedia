-- Prove2me | Theorems.Thm_KellyStochasticNetworks_MigrationDynamics_stationary_time_reversal
-- name    : KellyStochasticNetworks.MigrationDynamics.stationary_time_reversal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:46:43.260008+00:00
-- url     : https://prove2.me/theorems/a6943dfc-cc0b-4447-a4b9-5a7e7b49fd4d
-- title:
--   Proposition 1.1 — stationary countable-state process reversal
-- statement:
--   Let $(X_t)_{t\in\mathbb R}$ be a stationary Markov process on a countable state space $S$, defined on a probability space with transition rates $q(i,j)$ and equilibrium law $\pi$. As stipulated in Section 1.1, the process is irreducible, has strictly positive finite exit rates and is nonexplosive. The law $\pi$ is strictly positive and sums to one. Put $Y_t=X_{-t}$. Then $Y$ is a stationary Markov process with the same law $\pi$ and transition rates
--   $$q'(i,j)=\frac{\pi(j)q(j,i)}{\pi(i)},\qquad i,j\in S.$$
--   The conclusion includes the random-process Markov property and nonexplosion, as well as the infinitesimal transition rates.
--
--   This supplies the countable-state process reversal step needed for migration networks, whose occupancy space is infinite.
--
--   **Formalization Note** The diagonal entries of $q$ and $q'$ are zero, as in the source's jump-rate convention. Strict positivity of $\pi$ prevents division by zero. Endpoint conventions at jumps may be left- or right-continuous; deterministic-time finite-dimensional laws and the actual substitution $Y_t=X_{-t}$ are preserved. The imported definitions are reproduced verbatim as comments in the Lean file so the tool-free blind auditor can inspect them.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed pp. 16–17 (PDF pp. 24–25), Proposition 1.1; standing assumptions pp. 13–15 (PDF pp. 21–23)

import Definitions.Def_KellyStochasticNetworks_MigrationDynamics_Process

open MeasureTheory

/- BEGIN IMPORTED DEFINITIONS FOR BLIND AUDIT
The following are the exact declarations from the imported modules, with comments omitted.
They are quoted here only to expose dependencies to the tool-free auditor.

namespace KellyStochasticNetworks


def DetailedBalance {S : Type*} (π : S → ℝ) (q : S → S → ℝ) : Prop :=
  ∀ j k : S, π j * q j k = π k * q k j


def FullBalance {S : Type*} (π : S → ℝ) (q : S → S → ℝ) : Prop :=
  ∀ j : S, π j * (∑' k : S, q j k) = ∑' k : S, π k * q k j


noncomputable def reversedRates {S : Type*} (π : S → ℝ) (q : S → S → ℝ) : S → S → ℝ :=
  fun j k => π k * q k j / π j

end KellyStochasticNetworks

namespace KellyStochasticNetworks.MigrationDynamics


def LocallyFiniteJumpPath {S : Type*} (x : ℝ → S) : Prop :=
  (∀ a b : ℝ, a < b → ∃ D : Finset ℝ,
    ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b →
      (∀ d ∈ D, d ∉ Set.Icc s t) → x s = x t) ∧
  ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧
    ((∀ u ∈ Set.Ico t (t + ε), x u = x t) ∨
     (∀ u ∈ Set.Ioc (t - ε) t, x u = x t))


noncomputable def cylinder {Ω S : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ → Ω → S) {n : ℕ}
    (t : Fin n → ℝ) (x : Fin n → S) : ℝ :=
  (P {ω | ∀ i, X (t i) ω = x i}).toReal


def IsMarkovProcess {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S] [DecidableEq S]
    (P : Measure Ω) (X : ℝ → Ω → S) (q : S → S → ℝ) : Prop :=
  IsProbabilityMeasure P ∧
  (∀ t, Measurable (X t)) ∧
  (∀ᵐ ω ∂P, LocallyFiniteJumpPath (fun t => X t ω)) ∧
  (∀ i j, 0 ≤ q i j) ∧ (∀ i, q i i = 0) ∧
  (∀ i, Summable (q i) ∧ 0 < ∑' j, q i j) ∧
  (∀ i j, Relation.ReflTransGen (fun a b => 0 < q a b) i j) ∧
  ∃ K : ℝ → S → S → ℝ,
    (∀ h, 0 ≤ h → ∀ i, (∀ j, 0 ≤ K h i j) ∧ HasSum (K h i) 1) ∧
    (∀ i j, K 0 i j = if i = j then 1 else 0) ∧
    (∀ (n : ℕ) (t : Fin (n + 1) → ℝ) (x : Fin (n + 1) → S)
        (u : ℝ) (y : S), StrictMono t → t (Fin.last n) < u →
      (P {ω | (∀ i, X (t i) ω = x i) ∧ X u ω = y}).toReal =
        cylinder P X t x * K (u - t (Fin.last n)) (x (Fin.last n)) y) ∧
    (∀ i j, Tendsto
      (fun h : ℝ => (K h i j - if i = j then 1 else 0) / h)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (if i = j then -(∑' k, q i k) else q i j)))


def HasStationaryLaw {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
    (P : Measure Ω) (X : ℝ → Ω → S) (π : S → ℝ) : Prop :=
  IsProbabilityMeasure P ∧ (∀ t, Measurable (X t)) ∧
  (∀ i, 0 < π i) ∧ HasSum π 1 ∧
  ∀ t i, (P {ω | X t ω = i}).toReal = π i

end KellyStochasticNetworks.MigrationDynamics
END IMPORTED DEFINITIONS FOR BLIND AUDIT -/

namespace KellyStochasticNetworks.MigrationDynamics

theorem stationary_time_reversal {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S] [DecidableEq S]
    (P : Measure Ω) (X : ℝ → Ω → S) (q : S → S → ℝ) (π : S → ℝ)
    (hX : IsMarkovProcess P X q) (hπ : HasStationaryLaw P X π) :
    IsMarkovProcess P (fun t => X (-t)) (KellyStochasticNetworks.reversedRates π q) ∧
    HasStationaryLaw P (fun t => X (-t)) π := by sorry

end KellyStochasticNetworks.MigrationDynamics
