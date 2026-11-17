-- Prove2me | Theorems.Thm_NearLinIsing_Supplement_theorem_A_1
-- name    : NearLinIsing.Supplement.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:41:14.334118+00:00
-- url     : https://prove2.me/theorems/11b1ef60-67ea-4a59-8639-3b8100d82acd
-- title:
--   Theorem A.1 — XY counting and sampling at every coupling $K_e\ge0$ in work polynomial in $n$, $m$, $\sum_eK_e$, $1/\varepsilon$
-- statement:
--   There are two programs $Z$ and $S$ of the real-arithmetic machine of §2.6 and constants $C$, $k$, chosen before everything else, such that the following holds. Let $G$ be a simple graph with $n$ vertices and $m$ edges, given by indexed incidence lists, let $K_e\ge0$ be edge couplings and $0<\varepsilon<1/2$, and let
--
--   $$Z_{XY}(G,K)=\int\exp\Big(\sum_{uv\in E}K_{uv}\cos(\theta_u-\theta_v)\Big)\prod_{v\in V}\frac{d\theta_v}{2\pi}$$
--
--   with normalized Haar measure on $[0,2\pi)^V$. Run on $(G,\varepsilon,K)$ with a tape of independent uniform numbers:
--
--   1. $Z$ has measurable work and output, with probability at least $3/4$ it halts with an output $\hat Z$ satisfying $(1-\varepsilon)Z_{XY}(G,K)\le\hat Z\le(1+\varepsilon)Z_{XY}(G,K)$, and its expected work is at most $C\,(n+m+\sum_eK_e+1/\varepsilon)^k$;
--   2. $S$ has measurable work and output, its output law (the $n$ angles) is within total variation $\varepsilon$ of the XY spin law with couplings $K$, and its expected work is at most $C\,(n+m+\sum_eK_e+1/\varepsilon)^k$.
--
--   In particular, with $K_e=\log\beta$, both tasks take polynomial work at every fixed uniform $\beta\ge1$, including beyond the robust tree threshold of Theorem 1.2. No degree bound is assumed.
--
--   Differences from the source:
--   - encoding: there are randomized algorithms → there are programs Z and S of the deep-embedded machine `Program` with the stated properties; reason: an existence statement over algorithms needs programs as syntax
--   - reading: the computational model of §2.6 → unit-cost core real RAM plus rounding, elementary functions, uniform, geometric, Poisson and beta draws and Bessel ratios, with rational literals only; reason: the list of §2.6; fewer programs, so the claim is not weakened
--   - reading: approximate Z_XY(G, K) to relative error ε → (1 − ε)Z_XY ≤ Ẑ ≤ (1 + ε)Z_XY; reason: the paper's own form of relative error (§7, p. 40)
--   - reading: work polynomial in n, m, Σ_e K_e and 1/ε → expected work at most C(n + m + Σ_e K_e + 1/ε)^k with C, k chosen before G, K, ε; reason: work is expected work throughout the paper, and the recovery step (Lemma 5.10) is bounded only in expectation
--   - encoding: expected work → the integral over the uniform tape of the number of executed instructions, +∞ for a run that never halts; reason: the paper's work count
--   - encoding: the outputs are an estimate and a sample → measurability of the work and of the output maps is part of the conclusion; reason: otherwise the probability, the law and the integral would not be meaningful
--   - encoding: in particular, both tasks take polynomial work at every fixed uniform β ≥ 1 → not a separate conjunct; reason: it is the case K_e = log β of the statement, where (n + m + m log β + 1/ε)^k is polynomial in n, m, 1/ε for fixed β
--   - encoding: a simple graph G → a well-formed `IncGraph`, written into memory with ε and the couplings (K_e) by `graphInput`; reason: the input of §2.6
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, Theorem A.1 and Z_XY(G, K), Appendix A, p. 44; relative error, §7, p. 40; computational model, §2.6, p. 9

import Mathlib
import Definitions.Def_NearLinIsing_Supplement_Machine
import Definitions.Def_NearLinIsing_Supplement_SpinLaws

open MeasureTheory
open scoped ENNReal

namespace NearLinIsing

namespace Supplement

/-- **Theorem A.1** (XY tractability at every fixed temperature), p. 44.

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786, Theorem A.1 and the definition of `Z_XY(G, K)` above it, p. 44;
relative error as `(1 − ε)Z ≤ Ẑ ≤ (1 + ε)Z`, §7, p. 40; computational model, §2.6, p. 9.

There are two admissible programs `Z` (counting) and `S` (sampling) of the §2.6 machine and
constants `C`, `k`, chosen before everything else, such that for every well-formed simple graph
`G`, every family of edge couplings `K_e ≥ 0` and every `0 < ε < 1/2`, on the input
`(G, ε, (K_e)_e)`:
1. `Z` has measurable work and output, with probability at least `3/4` it halts with an output
   `Ẑ` (memory cell `−1`) satisfying `(1 − ε) Z_XY(G, K) ≤ Ẑ ≤ (1 + ε) Z_XY(G, K)`, where
   `Z_XY(G, K) = ∫ exp(∑_{uv∈E} K_uv cos(θ_u − θ_v)) ∏_v dθ_v/2π`, and its expected work is at
   most `C (n + m + ∑_e K_e + 1/ε)^k`;
2. `S` has measurable work and output, its output law (the `n` angles in memory cells
   `−1, …, −n`) is within total variation `ε` of the XY spin law with couplings `K`, and its
   expected work is at most `C (n + m + ∑_e K_e + 1/ε)^k`.

**Formalization Note.** "There are randomized algorithms … whose work is polynomial in `n`, `m`,
`∑_e K_e` and `1/ε`" is the existence of programs of the deep-embedded machine (`Program`,
rational literals; the continuous-spin primitives are allowed) with work at most
`C (n + m + ∑ K_e + 1/ε)^k`, `C` and `k` absolute. "Work" is read as expected work over the uniform
tape, as for every other work bound of the paper. No degree bound is assumed. The closing
sentence ("in particular … every fixed uniform `β ≥ 1`") is the case `K_e = log β` and follows
from this statement; it is not a separate conjunct. -/
theorem theorem_A_1 :
    ∃ Z S : Program, Z.Admissible ∧ S.Admissible ∧ ∃ C : ℝ, ∃ k : ℕ,
      ∀ G : IncGraph, G.WellFormed →
      ∀ K : Fin G.m → ℝ, (∀ e, 0 ≤ K e) →
      ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
        (Measurable (fun ω => ((haltTime Z (graphInput G (ε :: List.ofFn K)) ω : ℕ∞) : ℝ≥0∞)) ∧
          Measurable (outVec Z (graphInput G (ε :: List.ofFn K)) 1) ∧
          (3 / 4 : ℝ) ≤ tapeLaw.real {ω | HaltsOn Z (graphInput G (ε :: List.ofFn K)) ω ∧
            (1 - ε) * xyZ G K ≤ outVec Z (graphInput G (ε :: List.ofFn K)) 1 ω 0 ∧
            outVec Z (graphInput G (ε :: List.ofFn K)) 1 ω 0 ≤ (1 + ε) * xyZ G K} ∧
          expectedWork Z (graphInput G (ε :: List.ofFn K)) ≤
            ENNReal.ofReal (C * ((G.n : ℝ) + (G.m : ℝ) + ∑ e, K e + 1 / ε) ^ k)) ∧
        (Measurable (fun ω => ((haltTime S (graphInput G (ε :: List.ofFn K)) ω : ℕ∞) : ℝ≥0∞)) ∧
          Measurable (outVec S (graphInput G (ε :: List.ofFn K)) G.n) ∧
          tvM (outLaw S (graphInput G (ε :: List.ofFn K)) G.n) (xyLaw G K) ≤ ε ∧
          expectedWork S (graphInput G (ε :: List.ofFn K)) ≤
            ENNReal.ofReal (C * ((G.n : ℝ) + (G.m : ℝ) + ∑ e, K e + 1 / ε) ^ k)) := by sorry

end Supplement

end NearLinIsing
