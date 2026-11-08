-- Prove2me | Theorems.Thm_HardcoreSlices_theorem_1_4
-- name    : HardcoreSlices.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:37:51.51205+00:00
-- url     : https://prove2.me/theorems/ffce083c-1bca-41ea-9951-700e3ed724e6
-- title:
--   Theorem 1.4 (Main) — an FPAUS and an FPRAS for the hardcore model at $\lambda\lesssim1/\sqrt\Delta$
-- statement:
--   There are absolute constants $c>0$ and $\Delta_0$ such that for every $\Delta\ge\Delta_0$ there are two programs of the published unit-cost real RAM and constants $K,d$, chosen before the graph, with the following property. With high probability over a uniformly random $\Delta$-regular bipartite graph $G$ with sides of size $m$, for every real $\lambda\in(0,c/\sqrt\Delta]$:
--
--   1. **FPAUS.** For every $\varepsilon\in(0,1)$, on input $G,\lambda,\varepsilon$, the first program halts on every coin tape within $K(m+1+\log(1/\varepsilon))^d$ steps, and its output is within total variation $\varepsilon$ of the hardcore law $\mu_\lambda$.
--   2. **FPRAS.** For all $\varepsilon,\delta\in(0,1)$, on input $G,\lambda,\varepsilon,\delta$, the second program halts on every coin tape within $K(m+1+1/\varepsilon+\log(1/\delta))^d$ steps with a nonnegative output $\hat Z$, and
--   $$\Pr\bigl[(1-\varepsilon)Z_G(\lambda)\le\hat Z\le(1+\varepsilon)Z_G(\lambda)\bigr]\ge1-\delta.$$
--
--   This fugacity is well above the tree uniqueness threshold $\lambda_c(\Delta)\approx e/\Delta$.
--
--   Differences from the source:
--   - generalization: the sentence fixes no order between λ and the high-probability event → λ quantified inside the event, uniformly over its range; reason: the events the proof uses do not mention λ; a fixed-λ statement follows by specialization
--   - reading: polynomial time, no model named → worst-case steps of the published unit-cost real RAM, fair coins, rational literals, no bit size of λ; reason: λ is a real input and Definitions 2.12, 2.13 bound the time in n, ε, δ only; the algorithm is arithmetic
--   - reading: ∆ large but fixed; "there is" an algorithm → programs and K, d chosen for each ∆, before m, G, λ, ε, δ; reason: p.2 fixes ∆, the degree depends on ∆ through brute force for ε < C(∆)^{|X|} (p.27), and a program chosen after G would be trivial
--   - reading: λ ≲ 1/√∆ → 0 < λ ≤ c/√Δ, c absolute, no lower bound on λ; reason: p.2 defines ≲; the assumption λ > 1/∆ of p.26 is a case split of the proof
--   - reading: Ẑ ∈ R+ → 0 ≤ z on every tape; reason: on the accepted tapes z ≥ (1−ε)Z anyway, so this concerns only failing tapes
--   - encoding: random ∆-regular bipartite G, whp in n → published AlmostEvery on |X| = |Y| = m → ∞, with time in m; reason: n = 2m; the model is the uniform simple one of p.10
--   - encoding: the sampler outputs an independent set of G → the halted machine's bitmap 0, read as a vertex set through vIdx (hcLawOnBits); reason: Lean convention for the machine's output; the same law
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), Theorem 1.4 (Main), p.2

import Mathlib
import Definitions.Def_HardcoreSlices_IsFPRASRun

open Classical

namespace HardcoreSlices

open ExpanderBIS.RandomHardCore

/-- **Theorem 1.4 (Main).** Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), p.2: "Let `G = (X, Y, E)` be a random `∆`-regular bipartite graph for sufficiently large `∆ > 0`. Then with high probability over the randomness of `G`, there is both a fully
polynomial-time almost-uniform sampler (FPAUS) for the hardcore model on `G` and a fully polynomial-time randomized approximation scheme (FPRAS) for the partition function `ZG(λ)` of the hardcore model on `G` at
fugacity `λ ≲ 1/√∆`."

**Formalization Note.**
* `λ ≲ 1/√∆` is `λ ≤ c/√∆` for a sufficiently small constant (p.2): `c` and `Δ₀` are absolute and come first.
* "`∆` is large but fixed" (p.2): the two programs and the polynomial are chosen for each `∆`, before `m`, `G`, `λ`, `ε`, `δ`.
* `λ` is inside the high-probability event, as are `ε`, `δ`. No lower bound on `λ`: the proof's `λ > 1/∆` (p.26) is a case split.
* The machine is the published unit-cost real RAM with fair coins (`SubsetConvFPRAS.Machine`), both value oracles `0`, and the same program for every instance. Its input is `m`, `Δ`, the sorted adjacency lists (`graphInts`) and the
  reals `λ, ε` or `λ, ε, δ`. The sampler's output is bitmap `0`, a set of vertex numbers. The time bounds `timeS`, `timeC` are worst-case over the coins and have no bit size of `λ`.
* Whp is the published `AlmostEvery`: fixed sides `|X| = |Y| = m`, simple `∆`-regular bipartite graphs, uniform, as `m → ∞`. -/
theorem theorem_1_4 :
    ∃ c : ℝ, 0 < c ∧ ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ →
      ∃ (Ps Pc : SubsetConvFPRAS.Program) (K d : ℕ),
        SubsetConvFPRAS.Admissible Ps ∧ SubsetConvFPRAS.Admissible Pc ∧
        AlmostEvery Δ (fun m G =>
          ∀ lam : ℝ, 0 < lam → lam ≤ c / Real.sqrt Δ →
            (∀ ε : ℝ, 0 < ε → ε < 1 →
              IsFPAUSRun Ps (initGraph m Δ G [lam, ε]) (timeS K d m ε) (hcLawOnBits G lam) ε) ∧
            (∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
              IsFPRASRun Pc (initGraph m Δ G [lam, ε, δ]) (timeC K d m ε δ) (hardcoreZ G lam) ε δ)) := by sorry

end HardcoreSlices
