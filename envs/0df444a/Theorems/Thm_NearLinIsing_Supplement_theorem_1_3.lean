-- Prove2me | Theorems.Thm_NearLinIsing_Supplement_theorem_1_3
-- name    : NearLinIsing.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:39:51.603454+00:00
-- url     : https://prove2.me/theorems/eb5ced0c-b374-4d4d-a90b-fbfb206374e1
-- title:
--   Theorem 1.3 — Potts and random-cluster sampling for $0\le\beta-1\le0.1(\beta_{od}(q,\Delta)-1)$, expected work $\widetilde O(n+q^{O(1)}m)$
-- statement:
--   There are two programs $P$ and $R$ of the real-arithmetic machine of §2.6, using no continuous-spin primitive, and constants $C$, $k$, $a$, chosen before everything else, such that the following holds. Let $q\ge3$ be an integer and let $G$ be a simple graph on $n\ge1$ vertices with $m$ edges, given by indexed incidence lists, with maximum degree at most $\Delta\ge3$. Suppose
--
--   $$0\le\beta-1\le0.1\big(\beta_{od}(q,\Delta)-1\big),\qquad \beta_{od}(q,\Delta)=\frac{q-2}{(q-1)^{1-2/\Delta}-1},$$
--
--   and $0<\varepsilon<1/2$. Run on $(G,q,\beta,\varepsilon)$ with a tape of independent uniform numbers:
--
--   1. $P$ has measurable work and output, its output (a colouring in $[q]^V$) has law within total variation $\varepsilon$ of the zero-field Potts law $\mu_{q,\beta}(\sigma)\propto\beta^{m_=(\sigma)}$, and its expected work is at most $C\log^k(n/\varepsilon)\,(n+q^a m)$;
--   2. $R$ has measurable work and output, its output (an edge set $A\subseteq E$) has law within total variation $\varepsilon$ of the random-cluster law $\pi_{RC}(A)\propto(\beta-1)^{|A|}q^{k(A)}$ with edge activity $\beta-1$ and cluster weight $q$, and its expected work is at most $C\log^k(n/\varepsilon)\,(n+q^a m)$.
--
--   That is, both laws have $\varepsilon$-approximate samplers with expected work $\widetilde O(n+q^{O(1)}m)$, where the exponent of $q$ is absolute and independent of $\Delta$. The range reaches the order–disorder scale $\beta_{od}$ within a constant factor in the edge activity; $\beta=1$ is included.
--
--   Differences from the source:
--   - encoding: the zero-field Potts law (and the random-cluster law) has an ε-approximate sampler → there are programs P and R of the deep-embedded machine `Program` with the stated properties; reason: an existence statement over algorithms needs programs as syntax
--   - reading: the real-arithmetic model of §2.6 → unit-cost core real RAM plus rounding, elementary functions and uniform and geometric draws, with rational literals only and no Bessel ratio, Poisson or beta draw (`Discrete`); reason: §2.6 permits those three primitives only for continuous spins; fewer programs, so the claim is not weakened
--   - reading: Õ(n + q^{O(1)} m), the exponent of q absolute and independent of Δ → C log^k(n/ε)(n + q^a m) with C, k, a chosen before q, Δ, G, β, ε, and the same constants for both programs; reason: Õ suppresses polylogarithmic factors in n/ε (p. 1); the theorem states that a is absolute; the stronger reading for C and k (the proof fixes B₀ = 64⌈log₂ q⌉ and η = 1, δ = 1/2); one set of constants is the maximum of two
--   - encoding: expected work → the integral over the uniform tape of the number of executed instructions, +∞ for a run that never halts; reason: the paper's work count
--   - encoding: the output is a sample → measurability of the work and of the output map is part of the conclusion; reason: otherwise the law and the integral would not be meaningful
--   - encoding: G with n vertices → 1 ≤ n; reason: log(n/ε) presupposes n ≥ 1
--   - encoding: a simple graph G of maximum degree at most Δ → a well-formed `IncGraph` with `MaxDegLe Δ`, written into memory with q, β and ε by `graphInput`; the programs are not told Δ; reason: the input of §2.6
--   - encoding: colours [q] = {1, …, q} → 0, …, q − 1, the Potts law as a measure on ℝ^V on the colour vectors and the random-cluster law as a measure on ℝ^E on the indicator vectors; reason: injective relabellings; total variation is unchanged
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, Theorem 1.3 and βod, p. 3; Õ and ε-approximate sample, §1.1, p. 1; random-cluster law, §2.3, p. 9; computational model, §2.6, p. 9

import Mathlib
import Definitions.Def_NearLinIsing_Supplement_Machine
import Definitions.Def_NearLinIsing_Supplement_SpinLaws

open MeasureTheory
open scoped ENNReal

namespace NearLinIsing

namespace Supplement

/-- **Theorem 1.3** (Potts sampling below coexistence), p. 3.

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786, Theorem 1.3, p. 3; `Õ` and "ε-approximate sample", §1.1, p. 1;
the random-cluster law, §2.3, p. 9; computational model, §2.6, p. 9.

There are two admissible programs `P` (Potts) and `R` (random cluster) of the §2.6 machine that
use no continuous-spin primitive, and constants `C`, `k`, `a`, chosen before everything else, such
that for every integer `q ≥ 3`, every `Δ ≥ 3`, every well-formed simple graph `G` on `n ≥ 1`
vertices with maximum degree at most `Δ`, every `β` with `0 ≤ β − 1 ≤ 0.1 (βod(q, Δ) − 1)` and
every `0 < ε < 1/2`, on the input `(G, q, β, ε)`:
1. `P` has measurable work and output, its output law (the `n` colours in memory cells
   `−1, …, −n`) is within total variation `ε` of the zero-field Potts law `µ_{q,β}(σ) ∝ β^{m=(σ)}`
   on `[q]^V`, and its expected work is at most `C log^k(n/ε) (n + q^a m)`;
2. `R` has measurable work and output, its output law (the indicator vector of an edge set in
   memory cells `−1, …, −m`) is within total variation `ε` of the random-cluster law
   `π_RC(A) ∝ (β − 1)^{|A|} q^{k(A)}` on `A ⊆ E`, and its expected work is at most
   `C log^k(n/ε) (n + q^a m)`.

**Formalization Note.** "Has an ε-approximate sampler with expected work `Õ(n + q^{O(1)} m)`" is
the existence of a program of the deep-embedded machine (`Program`, rational literals, `Discrete`:
no Bessel ratio, Poisson or beta draw, which §2.6 permits only for continuous spins). `Õ(f)` is
read as `C (log(n/ε))^k f` and `q^{O(1)}` as `q^a`. The exponent `a` is absolute and independent
of `Δ`, as the theorem states; `C` and `k` are also absolute (the proof fixes `B₀ = 64⌈log₂ q⌉` and
Corollary 6.2's `η = 1`, `δ = 1/2`). The programs read `G`, `q`, `β`, `ε` from memory; they are
not told `Δ`. `β = 1` is included. Colours `[q]` are `0, …, q − 1`. `1 ≤ n` makes `log(n/ε)`
positive. -/
theorem theorem_1_3 :
    ∃ P R : Program, P.Admissible ∧ P.Discrete ∧ R.Admissible ∧ R.Discrete ∧
      ∃ C : ℝ, ∃ k a : ℕ,
      ∀ q : ℕ, 3 ≤ q → ∀ Δ : ℕ, 3 ≤ Δ →
      ∀ G : IncGraph, G.WellFormed → 1 ≤ G.n → G.MaxDegLe Δ →
      ∀ β : ℝ, 0 ≤ β - 1 → β - 1 ≤ 0.1 * (betaOd q Δ - 1) →
      ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
        (Measurable (fun ω => ((haltTime P (graphInput G [(q : ℝ), β, ε]) ω : ℕ∞) : ℝ≥0∞)) ∧
          Measurable (outVec P (graphInput G [(q : ℝ), β, ε]) G.n) ∧
          tvM (outLaw P (graphInput G [(q : ℝ), β, ε]) G.n) (pottsMeasure G q β) ≤ ε ∧
          expectedWork P (graphInput G [(q : ℝ), β, ε]) ≤
            ENNReal.ofReal (C * Real.log ((G.n : ℝ) / ε) ^ k *
              ((G.n : ℝ) + (q : ℝ) ^ a * (G.m : ℝ)))) ∧
        (Measurable (fun ω => ((haltTime R (graphInput G [(q : ℝ), β, ε]) ω : ℕ∞) : ℝ≥0∞)) ∧
          Measurable (outVec R (graphInput G [(q : ℝ), β, ε]) G.m) ∧
          tvM (outLaw R (graphInput G [(q : ℝ), β, ε]) G.m) (rcMeasure G q β) ≤ ε ∧
          expectedWork R (graphInput G [(q : ℝ), β, ε]) ≤
            ENNReal.ofReal (C * Real.log ((G.n : ℝ) / ε) ^ k *
              ((G.n : ℝ) + (q : ℝ) ^ a * (G.m : ℝ)))) := by sorry

end Supplement

end NearLinIsing
