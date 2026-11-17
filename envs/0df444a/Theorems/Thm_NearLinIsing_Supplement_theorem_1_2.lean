-- Prove2me | Theorems.Thm_NearLinIsing_Supplement_theorem_1_2
-- name    : NearLinIsing.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:39:02.392648+00:00
-- url     : https://prove2.me/theorems/b97dde31-fc89-4ede-8403-efac126a3a6e
-- title:
--   Theorem 1.2 — XY sampling at the robust tree threshold, expected work $\widetilde O(m+n\exp(O(\sqrt{\log(n/\varepsilon)})))$ for $\Delta\ge8$, $1<\beta\le\beta_{XY}(\Delta)$
-- statement:
--   There are a program $P$ of the real-arithmetic machine of §2.6 and constants $C$, $k$, $c$, chosen before everything else, such that the following holds. Let $G$ be a simple graph on $n\ge1$ vertices with $m$ edges, given by indexed incidence lists, with maximum degree at most $\Delta\ge8$. If $1<\beta\le\beta_{XY}(\Delta)$ and $0<\varepsilon<1/2$, then $P$, run on $(G,\beta,\varepsilon)$ with a tape of independent uniform numbers, has measurable work and output, its output law (the $n$ angles) satisfies
--
--   $$d_{TV}\big(\mathrm{Law}(\text{output}),\ \mu_{XY}\big)\le\varepsilon,\qquad \mu_{XY}(d\theta)=Z_{XY}^{-1}\beta^{\sum_{uv\in E}\cos(\theta_u-\theta_v)}\prod_{v\in V}\frac{d\theta_v}{2\pi}\ \text{ on }[0,2\pi)^V,$$
--
--   and its expected work is at most
--
--   $$C\,\log^k(n/\varepsilon)\,\Big(m+n\exp\big(c\sqrt{\log(n/\varepsilon)}\big)\Big).$$
--
--   That is, the XY law has an $\varepsilon$-approximate sampler with expected work $\widetilde O(m+n\exp(O(\sqrt{\log(n/\varepsilon)})))$ up to and including the robust tree threshold $\beta_{XY}(\Delta)$ of (1). For $\varepsilon=n^{-O(1)}$ this is almost-linear work.
--
--   Differences from the source:
--   - encoding: the XY law has an ε-approximate sampler → there is a program of the deep-embedded machine `Program` (finite instruction list, input only through memory) with the stated properties; reason: an existence statement over algorithms needs programs as syntax
--   - reading: the real-arithmetic model of §2.6 → unit-cost core real RAM plus rounding, elementary functions, uniform, geometric, Poisson and beta draws and Bessel ratios, with rational literals only; reason: the list of §2.6; restricting literals only shrinks the set of programs, so the claim is not weakened
--   - reading: Õ(m + n exp(O(√log(n/ε)))) → C log^k(n/ε)(m + n exp(c√log(n/ε))) with C, k, c chosen before Δ, G, β, ε; reason: Õ suppresses polylogarithmic factors in n/ε (p. 1); the stronger reading, as for the base goal; the proof fixes η = 1/8 and λmax(AW) ≤ 384/143
--   - encoding: expected work → the integral over the uniform tape of the number of executed instructions, +∞ for a run that never halts; reason: the paper's work count; a non-halting run cannot satisfy the bound
--   - encoding: the output is a sample → measurability of the work and of the output map is part of the conclusion; reason: otherwise the law and the integral would not be meaningful
--   - encoding: G with n vertices → 1 ≤ n; reason: log(n/ε) presupposes n ≥ 1
--   - encoding: a simple graph G of maximum degree at most Δ → a well-formed `IncGraph` with `MaxDegLe Δ`, written into memory with β and ε by `graphInput`; the program is not told Δ; reason: the input of §2.6; a program can compute the maximum degree itself in O(n) work
--   - encoding: μ_XY ∝ β^{Σ cos(θ_u−θ_v)} ∏ dθ_v/2π → `xyLaw G (fun _ => log β)`, density exp(Σ log β cos(θ_u−θ_v))/Z against normalized Haar measure on [0, 2π)^V; reason: β^y = exp(y log β) for β > 0; same law
--   - encoding: βXY(Δ), the unique β > 1 with (Δ−1)I₁(log β)/I₀(log β) = 1 → sup{b ≥ 1 : (Δ−1)I₁(log b)/I₀(log b) ≤ 1}; reason: I₁/I₀ increases strictly from 0 to 1, so both are the same number
--   - encoding: I_k(x) = (1/2π)∫e^{x cos θ}cos(kθ)dθ → the published power series `besselI`; reason: equal for integer k
--   - encoding: angles θ ∈ [0, 2π)^V → real output cells; reason: the target law gives no mass outside [0, 2π)^V, so total variation is unchanged
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, Theorem 1.2, p. 2; Õ and ε-approximate sample, §1.1, p. 1; computational model, §2.6, p. 9

import Mathlib
import Definitions.Def_NearLinIsing_Supplement_Machine
import Definitions.Def_NearLinIsing_Supplement_SpinLaws

open MeasureTheory
open scoped ENNReal

namespace NearLinIsing

namespace Supplement

/-- **Theorem 1.2** (XY sampling at the robust tree threshold), p. 2.

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786, Theorem 1.2, p. 2; `Õ` and "ε-approximate sample", §1.1, p. 1;
computational model, §2.6, p. 9.

There is an admissible program `P` of the §2.6 machine and constants `C`, `k`, `c`, chosen before
everything else, such that for every `Δ ≥ 8`, every well-formed simple graph `G` on `n ≥ 1`
vertices with maximum degree at most `Δ`, every `1 < β ≤ βXY(Δ)` and every `0 < ε < 1/2`, the run
of `P` on the input `(G, β, ε)` has measurable work and output, its output law (the `n` angles in
memory cells `−1, …, −n`) is within total variation `ε` of the XY law
`µ_XY(dθ) ∝ β^{∑_{uv∈E} cos(θ_u − θ_v)} ∏_v dθ_v/2π` on `[0, 2π)^V`, and its expected work is at
most `C log^k(n/ε) (m + n exp(c √log(n/ε)))`, i.e. `Õ(m + n exp(O(√log(n/ε))))`.

**Formalization Note.** "Has an ε-approximate sampler" is the existence of a program of the
deep-embedded machine `Program` (§2.6 primitives, rational literals, including the continuous-spin
primitives: Bessel ratios, Poisson and beta draws). `Õ(f)` is read as `C (log(n/ε))^k f`, with the
`O` inside the exponential an existential constant `c`. The constants `C, k, c` and the program do
not depend on `Δ`, `G`, `β` or `ε` (the proof, p. 32, fixes `η = 1/8` and `λmax(AW) ≤ 384/143`).
The program reads `G` (indexed incidence lists), `β` and `ε` from memory (`graphInput`); it is not
told `Δ`. `1 ≤ n` makes `log(n/ε)` positive. Work is expected work over the uniform tape, `⊤` if
the run fails to halt with positive probability. -/
theorem theorem_1_2 :
    ∃ P : Program, P.Admissible ∧ ∃ C : ℝ, ∃ k : ℕ, ∃ c : ℝ,
      ∀ Δ : ℕ, 8 ≤ Δ → ∀ G : IncGraph, G.WellFormed → 1 ≤ G.n → G.MaxDegLe Δ →
      ∀ β : ℝ, 1 < β → β ≤ betaXY Δ →
      ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
        Measurable (fun ω => ((haltTime P (graphInput G [β, ε]) ω : ℕ∞) : ℝ≥0∞)) ∧
        Measurable (outVec P (graphInput G [β, ε]) G.n) ∧
        tvM (outLaw P (graphInput G [β, ε]) G.n) (xyLaw G (fun _ => Real.log β)) ≤ ε ∧
        expectedWork P (graphInput G [β, ε]) ≤
          ENNReal.ofReal (C * Real.log ((G.n : ℝ) / ε) ^ k *
            ((G.m : ℝ) + (G.n : ℝ) * Real.exp (c * Real.sqrt (Real.log ((G.n : ℝ) / ε))))) := by sorry

end Supplement

end NearLinIsing
