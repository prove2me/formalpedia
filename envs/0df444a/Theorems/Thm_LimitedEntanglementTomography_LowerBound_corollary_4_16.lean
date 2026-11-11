-- Prove2me | Theorems.Thm_LimitedEntanglementTomography_LowerBound_corollary_4_16
-- name    : LimitedEntanglementTomography.LowerBound.corollary_4_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:26.068761+00:00
-- url     : https://prove2.me/theorems/de31abbb-46f0-435a-bca9-fcd6f2bb23ae
-- title:
--   Corollary 4.16 — unrestricted joint measurements need $n\gtrsim d^2/\varepsilon^2$
-- statement:
--   There is an absolute constant $c>0$ such that for every $d\ge2$ and $0<\varepsilon\le1/4$: any tomography procedure using $n$ copies that estimates every $d$-dimensional state to trace distance at most $\varepsilon$ with probability at least $2/3$ satisfies
--   $$n\ge c\,\frac{d^2}{\varepsilon^2}.$$
--   This holds both for every protocol of Definition 1.1 (with any $k$) and even when a single joint POVM, with any standard Borel outcome space and a measurable state-valued estimate, acts on all $n$ copies.
--
--   It covers the finitely many dimensions left out of the Gaussian-prior argument in the proof of Theorem 1.3.
--
--   Differences from the source:
--   - reading: "any tomography protocol using n copies … This holds even if a single joint POVM may act on all n copies" → two conclusions with one constant: for every single joint POVM on n copies with a measurable state-valued estimator, and for every protocol of Definition 1.1 using at most n copies; reason: both readings of "protocol" in the sentence are stated
--   - encoding: Definition 1.1: rounds j = 1,…,T with 1 ≤ t_j ≤ k, a random stopping time, Σ t_j ≤ n almost surely → a protocol has a horizon `rounds`; a round with t_j = 0 makes no measurement (this encodes stopping); the outcome kernels are part of the data and are pinned to the Born laws on every state; Σ t_j ≤ n almost surely under every state; one standard Borel outcome space Out serves every round, and the POVM effects are measurable in the whole history; reason: T ≤ n since active rounds use at least one copy, so a horizon loses nothing; a round with t_j = 0 followed by measuring rounds is equivalent to the same protocol without that round, so the class of experiments is unchanged; the kernel exists and is unique on states for every source protocol; every standard Borel outcome space embeds Borel-isomorphically into one (for instance into ℝ), and a POVM family measurable on the histories with t_j = t extends to all histories by a fixed POVM
--   - encoding: probabilities and expectations of nonnegative quantities in ℝ → values of measures in [0,∞] (ENNReal); reason: a probability is the same number; inequalities are unchanged
-- source:
--   Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, Tight Lower Bounds for State Tomography with Limited Entanglement, STOC 2027 submission #1625 (October 2026), source.pdf SHA-256 bdd8884c95899a0c563507d1c005e0dee86e418d52478a2e9e6682bb1f9d29c3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1625.pdf, §4.4, printed p.17 / PDF p.19, Corollary 4.16 (eq. (32))

import Mathlib
import Definitions.Def_LimitedEntanglementTomography_LowerBound_Protocol

open scoped ENNReal ComplexOrder

/-!
Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, *Tight Lower Bounds for State
Tomography with Limited Entanglement*, STOC 2027 submission #1625 (October 2026), Corollary 4.16, printed p.17 / PDF p.19, eq. (32).
-/

namespace LimitedEntanglementTomography.LowerBound

open MeasureTheory ProbabilityTheory Matrix ShadowTomography.ClassicalLB

/-- **Corollary 4.16.** There is an absolute constant `c > 0` such that for every `d ≥ 2`, every
`0 < ε ≤ 1/4` and every `n`: (i) every single joint POVM on all `n` copies, with a measurable
state-valued estimator, that is within trace distance `ε` with probability `≥ 2/3` on every
state, and (ii) every protocol of Definition 1.1 using at most `n` copies with an estimator
solving Problem 1.2, satisfy `n ≥ c d² / ε²`. -/
theorem corollary_4_16 :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ), 2 ≤ d → ∀ (ε : ℝ), 0 < ε → ε ≤ 1 / 4 → ∀ n : ℕ,
      (∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (M : POVM (Fin n → Fin d) Ω)
          (est : Ω → Op d), Measurable est → (∀ ω, WildeQIT.IsDensityOperator (est ω)) →
          (∀ ρ : Op d, WildeQIT.IsDensityOperator ρ →
            2 / 3 ≤ bornProb M (tensorPow ρ n) {ω | traceDist ρ (est ω) ≤ ε}) →
          c * ((d : ℝ) ^ 2 / ε ^ 2) ≤ n) ∧
      (∀ (k : ℕ) (P : Protocol d k) (est : P.Estimator), P.UsesAtMost n → P.Solves est ε →
          c * ((d : ℝ) ^ 2 / ε ^ 2) ≤ n) := by sorry

end LimitedEntanglementTomography.LowerBound
