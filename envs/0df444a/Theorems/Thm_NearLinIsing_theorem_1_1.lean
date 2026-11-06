-- Prove2me | Theorems.Thm_NearLinIsing_theorem_1_1
-- name    : NearLinIsing.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:45:43.344965+00:00
-- url     : https://prove2.me/theorems/a440d984-7641-4c6b-8e9f-90f154bfabd4
-- title:
--   Theorem 1.1 — Ising sampling at the tree-uniqueness threshold
-- statement:
--   There are constants $c_T>0$ and $C$, chosen before everything else, such that the following holds. Let $G$ be a simple graph on $n\ge1$ vertices with $m$ edges, given by incidence lists, with maximum degree at most $\Delta\ge3$. If $1<\beta\le\Delta/(\Delta-2)$, then for every $0<\varepsilon<1/2$ the program `isingSampler` with constant $c_T$, run on an i.i.d. uniform tape, has measurable output and measurable cost, its output law satisfies
--
--   $$d_{TV}\big(\mathrm{Law}(\text{output}),\ \mu_{\mathrm{Ising}}\big)\le\varepsilon,$$
--
--   and its expected work is at most
--
--   $$C\,\big(n+m\log^3(n/\varepsilon)\big).$$
--
--   Here $\mu_{\mathrm{Ising}}(\sigma)\propto\beta^{m_=(\sigma)}$ is the zero-field law on all of $\{-1,1\}^V$. The range includes the critical point $\beta=\Delta/(\Delta-2)$, where single-site Glauber dynamics can need $\Omega(n^{3/2})$ updates.
--
--   Differences from the source:
--   - encoding: the law has an ε-approximate sampler → the statement is about the concrete `isingSampler`, whose chain length carries the unnamed constant c_T; reason: it is the paper's algorithm (proof, p. 22), and it implies the existential
--   - encoding: expected work in the real-arithmetic model of §2.6 → the expected operation count of `Prog` over the uniform tape, as a lower integral; reason: every charged primitive is O(1) in the paper's model
--   - encoding: the output is a sample → measurability of the output events and of the cost is part of the conclusion; reason: otherwise the law and the integral would not be meaningful
--   - encoding: G with n vertices → 1 ≤ n; reason: log(n/ε) presupposes n ≥ 1
--   - reading: O(n + m log³(n/ε)) → one constant C, independent of Δ, G, β and ε; reason: the stronger reading; the proof's constants depend only on η = 1/2 and δ = 1/6, and Δ enters only through (Δ−1)r ≤ 1
--   - encoding: spins in {−1, 1} → `Bool` spins; reason: the law depends only on equality of spins
--   - encoding: isolated vertices are removed first and sampled independently (§2.6) → every vertex gets its spin from recovery, an isolated vertex as a singleton component; reason: same law and same order of work
--   - encoding: a simple graph G given by indexed incidence lists (p. 1, §2.6) with maximum degree at most Δ → a well-formed `IncGraph` (`WellFormed`: loopless, no repeated pair, incidence lists exact) with `MaxDegLe Δ`; reason: reading R5; the same graphs
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, Theorem 1.1, p. 2; algorithm in the proof of Theorem 1.1, p. 22

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_NearLinIsing_isingSampler

open MeasureTheory
open scoped ENNReal

namespace NearLinIsing

/-- **Theorem 1.1** (Ising sampling at the tree-uniqueness threshold), p. 2.

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786, Theorem 1.1, p. 2; algorithm from the proof of Theorem 1.1, p. 22.

There are constants `cT > 0` and `C`, chosen before everything else, such that for every `Δ ≥ 3`,
every well-formed simple graph `G` on `n ≥ 1` vertices given by incidence lists with maximum degree
at most `Δ`, every `1 < β ≤ Δ/(Δ−2)` and every `0 < ε < 1/2`, the concrete program
`isingSampler cT G β ε` run on an i.i.d. uniform tape has measurable output events and measurable
cost, its output law is within total variation `ε` of the zero-field Ising law
`µ(σ) ∝ β^{m=(σ)}` on `{−1,1}^V`, and its expected work is at most `C (n + m log³(n/ε))`.

**Formalization Note.** Reading R1: "has an ε-approximate sampler" is stated for the paper's own
algorithm `isingSampler`, whose chain length `⌈cT · N · log²(N/ε)⌉` (`N = 10m`) carries the unnamed
constant of `O(N log²(N/ε))`. Readings R2–R3: the cost model of `Prog`. Reading R4: expected work is
the lower integral of the operation count over the tape law; `1 ≤ n` makes `log(n/ε)` meaningful.
`C` does not depend on `Δ` (the proof's constants depend only on `η = 1/2`, `δ = 1/6`). Spins are
`Bool`. -/
theorem theorem_1_1 :
    ∃ cT : ℝ, 0 < cT ∧ ∃ C : ℝ,
      ∀ Δ : ℕ, 3 ≤ Δ → ∀ G : IncGraph, G.WellFormed → 1 ≤ G.n → G.MaxDegLe Δ →
      ∀ β : ℝ, 1 < β → β ≤ (Δ : ℝ) / ((Δ : ℝ) - 2) →
      ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
        (∀ σ : Fin G.n → Bool, MeasurableSet {τ : Tape | samplerOut cT G β ε τ = σ}) ∧
        Measurable (fun τ : Tape => runCost (isingSampler cT G β ε) τ) ∧
        MarkovMixing.tvDist (fun σ => tapeLaw.real {τ : Tape | samplerOut cT G β ε τ = σ})
            (G.isingLaw β) ≤ ε ∧
        ∫⁻ τ, (runCost (isingSampler cT G β ε) τ : ℝ≥0∞) ∂tapeLaw ≤
          ENNReal.ofReal (C * ((G.n : ℝ) + (G.m : ℝ) * Real.log ((G.n : ℝ) / ε) ^ 3)) := by sorry

end NearLinIsing
