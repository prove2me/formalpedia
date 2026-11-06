-- Prove2me | Theorems.Thm_NearLinIsing_proposition_4_6
-- name    : NearLinIsing.proposition_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:45:29.489831+00:00
-- url     : https://prove2.me/theorems/75d1da2e-bfe1-4c13-8a4b-930a9e79cb63
-- title:
--   Proposition 4.6 — Ising work
-- statement:
--   Let $G$ be a well-formed graph without isolated vertices that contains a cycle, with maximum degree at most $\Delta\ge3$.
--
--   1. For $r>0$ with $(\Delta-1)r\le1$, $N=10m$ and every $t$, the concrete simulation outputs a family with law exactly $\delta_\emptyset P^t$, the chain of Theorem 1.5 on the cycle model of $H$, and its expected work is at most $C_6(m+t\log n)$ with an absolute constant $C_6$.
--   2. Spin recovery has expected work at most $C_7m$ with an absolute constant $C_7$.
--   3. For every chain-length constant $c_T>0$ there is $C'$ such that for every $1<\beta\le\Delta/(\Delta-2)$ and $0<\varepsilon<1/2$ the full sampler, at the first horizon $t=\lceil c_TN\log^2(N/\varepsilon)\rceil$, has expected work at most $C'm\log^3(n/\varepsilon)$.
--
--   This is the accounting that turns chain steps into work.
--
--   Differences from the source:
--   - encoding: the cycle chain can be simulated → the output law is exactly δ_∅P^t and the cost is measurable with bounded expectation, for the concrete `simulateChain`; reason: this is what simulation means here
--   - encoding: n, m refer to the graph after preprocessing (§2.6), and G contains a cycle (§4) → `∀ v, 1 ≤ G.deg v` and `G.HasCycle` are binders; reason: the standing assumptions of pp. 10 and 18
--   - encoding: G of maximum degree at most Δ ≥ 3, flow weight r with (Δ − 1)r ≤ 1 (Proposition 4.1) → a well-formed `IncGraph` with `MaxDegLe Δ`, and clause 1 for every r > 0 with (Δ − 1) r ≤ 1; reason: the input format of §2.6 and the hypotheses of Proposition 4.1; r = (β − 1)/(β + 1) ranges over exactly this set
--   - generalization: spin recovery costs O(m) (with the weights t_e = r) → the bound C₇ m holds for `recoverSpins` with arbitrary weights `tw`; reason: the recovery program charges the same for every weight; t_e = r is an instance
--   - generalization: O(m log³(n/ε)) at the first mixing horizon of Theorem 1.5 → for every chain-length constant cT > 0 there is C′ with work ≤ C′ m log³(n/ε) at t = ⌈cT N log²(N/ε)⌉; reason: the first horizon is t = ⌈C₁ N log²(N/ε)⌉ for the constant C₁ of Theorem 1.5, which is the instance cT = C₁
--   - reading: O(m + t log n), O(m), O(m log³(n/ε)) → constants C₆, C₇ absolute and C′ depending only on cT, all independent of Δ, G, r, β, ε; reason: the stronger reading; the construction is linear for every Δ and log m ≤ 2 log n, log(10m/ε) = O(log(n/ε))
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, Proposition 4.6 and its proof, pp. 21–22

import Mathlib
import Definitions.Def_NearLinIsing_isingSampler

open MeasureTheory
open scoped ENNReal

namespace NearLinIsing

/-- **Proposition 4.6** (Ising work), p. 21.

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786, Proposition 4.6 and its proof, pp. 21–22.

Standing assumptions (§2.6, p. 10, and §4, p. 18): `G` is well formed, has no isolated vertex,
contains a cycle, and has maximum degree at most `Δ ≥ 3`.
1. For `r > 0` with `(Δ − 1) r ≤ 1`, `N = 10m` and every `t`, the concrete simulation
   `simulateChain G r N t` (port-graph construction, then `t` chain steps from `∅`) outputs a
   family whose law is exactly `δ_∅ P^t`, the law of the insertion–deletion chain of Theorem 1.5
   on the cycle model of `H = portGraph G r`, and its expected work is at most
   `C₆ (m + t log n)` with an absolute constant `C₆`.
2. Spin recovery costs `O(m)`: for every edge set `F` and all weights, the expected work of
   `recoverSpins` is at most `C₇ m` with an absolute constant `C₇`.
3. For every chain-length constant `cT > 0` there is `C'` such that, for every `1 < β ≤ Δ/(Δ−2)` and
   `0 < ε < 1/2`, the full program `isingSampler cT G β ε` (the simulation at the first horizon
   `t = ⌈cT N log²(N/ε)⌉` of Theorem 1.5, projection and spin recovery) has expected work at most
   `C' m log³(n/ε)`.

**Formalization Note.** "Taking N = 10m in Theorem 1.5, the cycle chain … can be simulated" is
stated as exactness of the output law plus the expected-work bound; each cost is stated to be
measurable, so its lower integral is its expectation. `G` contains a cycle is
written `G.HasCycle` (a nonempty even subgraph). -/
theorem proposition_4_6 :
    (∃ C₆ : ℝ, 0 < C₆ ∧
      ∀ Δ : ℕ, 3 ≤ Δ → ∀ G : IncGraph, G.WellFormed → G.MaxDegLe Δ → G.HasCycle →
      (∀ v, 1 ≤ G.deg v) → ∀ r : ℝ, 0 < r → ((Δ : ℝ) - 1) * r ≤ 1 → ∀ t : ℕ,
        (∀ 𝒳 : Finset (portGraph G r).Cyc,
          MeasurableSet {τ : Tape |
            famSet (portGraph G r) (runVal (simulateChain G r (10 * G.m) t) τ).2 =
              𝒳.map (Function.Embedding.subtype _)} ∧
          tapeLaw.real {τ : Tape |
            famSet (portGraph G r) (runVal (simulateChain G r (10 * G.m) t) τ).2 =
              𝒳.map (Function.Embedding.subtype _)} =
            (portGraph G r).cycleModel.stepLaw (10 * G.m) t 𝒳) ∧
        Measurable (fun τ : Tape => runCost (simulateChain G r (10 * G.m) t) τ) ∧
        ∫⁻ τ, (runCost (simulateChain G r (10 * G.m) t) τ : ℝ≥0∞) ∂tapeLaw ≤
          ENNReal.ofReal (C₆ * ((G.m : ℝ) + t * Real.log G.n))) ∧
    (∃ C₇ : ℝ, 0 < C₇ ∧
      ∀ G : IncGraph, G.WellFormed → G.HasCycle → (∀ v, 1 ≤ G.deg v) →
      ∀ (tw : ℕ → ℝ) (F : Finset (Fin G.m)),
        Measurable (fun τ : Tape => runCost (recoverSpins G tw (encF G F)) τ) ∧
        ∫⁻ τ, (runCost (recoverSpins G tw (encF G F)) τ : ℝ≥0∞) ∂tapeLaw ≤
          ENNReal.ofReal (C₇ * (G.m : ℝ))) ∧
    (∀ cT : ℝ, 0 < cT → ∃ C' : ℝ, 0 < C' ∧
      ∀ Δ : ℕ, 3 ≤ Δ → ∀ G : IncGraph, G.WellFormed → G.MaxDegLe Δ → G.HasCycle →
      (∀ v, 1 ≤ G.deg v) → ∀ β : ℝ, 1 < β → β ≤ (Δ : ℝ) / ((Δ : ℝ) - 2) →
      ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
        Measurable (fun τ : Tape => runCost (isingSampler cT G β ε) τ) ∧
        ∫⁻ τ, (runCost (isingSampler cT G β ε) τ : ℝ≥0∞) ∂tapeLaw ≤
          ENNReal.ofReal (C' * (G.m : ℝ) * Real.log ((G.n : ℝ) / ε) ^ 3)) := by sorry

end NearLinIsing
