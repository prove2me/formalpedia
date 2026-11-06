-- Prove2me | Theorems.Thm_MemQueryFeas_theorem_1
-- name    : MemQueryFeas.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:36:53.099977+00:00
-- url     : https://prove2.me/theorems/403ac49e-3072-436d-969c-7771f459f397
-- title:
--   Theorem 1 — with $d^{1+\delta}\log(1/\epsilon)$ bits, accuracy-$\epsilon$ feasibility needs $(d\log(1/\epsilon))^{\tilde\Omega(d^{(1-\delta)/8})}$ queries
-- statement:
--   **Setting.** A learner must find a point of an unknown convex set $Q$ contained in the closed unit ball $B_d(0,1)\subseteq\mathbb R^d$ and containing a ball of radius $\varepsilon$. It may query points $x_t\in B_d(0,1)$; a separation oracle answers Success if $x_t\in Q$ and otherwise returns $g_t$ with $g_t^\top(y-x_t)<0$ for all $y\in Q$. The learner keeps an $M$-bit memory between rounds and may use fresh randomness in each round.
--
--   **Theorem.** There are constants $c>0$, $C\ge0$ and $d_0$ such that for all $d\ge d_0$, all $0<\varepsilon\le e^{-d}$, all $\delta\in[0,1]$ and every memory size
--   $$
--   M\le d^{1+\delta}\log(1/\varepsilon),
--   $$
--   writing
--   $$
--   B(d,\varepsilon,\delta)=\big(d\log(1/\varepsilon)\big)^{c\,d^{(1-\delta)/8}/\log^C d},
--   $$
--   1. every randomized $M$-bit algorithm that, against every instance and every valid (measurable) adaptive separation oracle, queries a point of $Q$ among its first $T$ queries with probability at least $2/3$ has $T\ge B(d,\varepsilon,\delta)$;
--   2. every (measurable) deterministic $M$-bit algorithm that, against every instance and every valid non-adaptive separation oracle, queries a point of $Q$ among its first $T$ queries has $T\ge B(d,\varepsilon,\delta)$.
--
--   Here $\log$ is the base-2 logarithm. With linear memory the learner needs $(d\ln(1/\varepsilon))^{\tilde\Omega(d^{1/8})}$ queries, and the exponent decays as $d^{(1-\delta)/8}$ as memory grows, which matches the recursive cutting-plane algorithms of Blanchard, Zhang and Jaillet up to the factor $1/8$.
--
--   **Formalization Note** The exponent $\tilde\Omega(d^{(1-\delta)/8})$ is pinned as $c\,d^{(1-\delta)/8}/(\log_2 d)^C$ with constants uniform in $\varepsilon$, $\delta$ and $M$.
--
--   Differences from the source:
--   - reading: Ω̃(d^{(1−δ)/8}) (hiding polylog d factors) and "d sufficiently large" → ∃ c > 0, C ∈ ℕ, d₀ with exponent c·d^{(1−δ)/8}/(log₂ d)^C, uniform in ε, δ, M; reason: the precise meaning of Ω̃ hiding polylog d factors
--   - generalization: "either uses M = d^{1+δ} log 1/ϵ bits of memory or makes at least … queries" → every M ≤ d^{1+δ} log₂(1/ε) forces T ≥ B; reason: covers the printed budget and every smaller one; the proof runs at M = d^{1+δ} ln(1/ε) and absorbs constant factors through δ
--   - generalization: success against every valid (time-dependent, randomized, adaptive) oracle → success required only against deterministic, measurable adaptive oracles valid at every point; reason: a weaker success hypothesis; randomized oracles are mixtures of deterministic ones and the proof's oracles are of this kind
--   - generalization: Q contains a Euclidean ball of radius ε → Q contains a closed ball of radius ε; reason: fewer instances in the success hypothesis; the proof's ball is closed
--   - generalization: i.i.d. fresh randomness for ψ_query and ψ_update → one fresh draw per round, shared by both maps; reason: separate draws are the case of a product space
--   - reading: randomized and deterministic algorithms (measurability not stated) → measurable maps (RandMemAlg fields; DetMemAlg.IsMeasurable in clause 2); reason: standing convention: probabilities and information quantities of runs (§3) presuppose measurability
--   - encoding: Success; {0,1}^M with Memory_1 = 0; rounds t ≥ 1; B_d(0,1); "makes at least N queries" → none; Fin M → Bool initialized all-false; rounds from 0; the closed ball; the success horizon T satisfies T ≥ N; reason: Lean conventions; the same instances
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Theorem 1, p.2 (PDF p.3); proof §4.5, pp.29–31

import Mathlib
import Definitions.Def_MemQueryFeas_SucceedsAdaptive
import Definitions.Def_MemQueryFeas_SucceedsNonAdaptive
import Definitions.Def_MemQueryFeas_DetMemAlg_IsMeasurable

namespace MemQueryFeas

/-- **Theorem 1 (memory/query-complexity tradeoff for high-accuracy feasibility).** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Theorem 1,
p.2 (PDF p.3): "Let `d` be sufficiently large and `0 < ϵ ≤ e^{−d}`. Then, for any `δ ∈ [0, 1]`, any
algorithm that solves feasibility problems up to accuracy `ϵ` with probability `2/3` either uses
`M = d^{1+δ} log 1/ϵ` bits of memory or makes at least `(d log 1/ϵ)^{Ω̃(d^{(1−δ)/8})}` queries, where
`Ω̃` only hides polylog `d` factors. Here, the considered feasibility oracles may be adaptive in the
learner's queries. For deterministic algorithms, the oracle can be non-adaptive."

There are constants `c > 0`, `C ∈ ℕ` and `d₀` such that for all `d ≥ d₀`, `0 < ε ≤ e^{−d}`,
`δ ∈ [0,1]` and `M ≤ d^{1+δ} log₂(1/ε)`, with `B := (d log₂(1/ε))^{c d^{(1−δ)/8}/(log₂ d)^C}`:
(a) every randomized `M`-bit algorithm that succeeds within `T` queries with probability `2/3`
against every valid (measurable) adaptive oracle has `T ≥ B`; (b) every measurable deterministic
`M`-bit algorithm that succeeds within `T` queries against every valid non-adaptive oracle has
`T ≥ B`.

**Formalization Note.** `Ω̃` and "sufficiently large" are pinned by the existential constants
`c, C, d₀`, uniform in `ε, δ, M`. "Uses `M` bits … or makes at least" becomes: if
`M ≤ d^{1+δ} log₂(1/ε)` then `T ≥ B`. log is base 2 (Notations, p.7). -/
theorem theorem_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℕ, ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ ε : ℝ, 0 < ε → ε ≤ Real.exp (-(d : ℝ)) →
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      ∀ M : ℕ, (M : ℝ) ≤ (d : ℝ) ^ (1 + δ) * Real.logb 2 (1 / ε) →
        (∀ (alg : RandMemAlg d M) (T : ℕ), SucceedsAdaptive alg ε T →
          ((d : ℝ) * Real.logb 2 (1 / ε)) ^
              (c * (d : ℝ) ^ ((1 - δ) / 8) / (Real.logb 2 d) ^ C) ≤ (T : ℝ)) ∧
        (∀ (alg : DetMemAlg d M) (T : ℕ), alg.IsMeasurable → SucceedsNonAdaptive alg ε T →
          ((d : ℝ) * Real.logb 2 (1 / ε)) ^
              (c * (d : ℝ) ^ ((1 - δ) / 8) / (Real.logb 2 d) ^ C) ≤ (T : ℝ)) := by sorry

end MemQueryFeas
