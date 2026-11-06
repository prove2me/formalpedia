-- Prove2me | Theorems.Thm_HMajConsensus_lemma_6_2_amplification_phase
-- name    : HMajConsensus.lemma_6_2_amplification_phase
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:15:45.801824+00:00
-- url     : https://prove2.me/theorems/61823c51-48b0-47fc-b70d-e47d7bac5b43
-- title:
--   Lemma 6.2 — from a good configuration the phase succeeds within $T=2\lceil\frac{32}{c\gamma(0)}\ln\frac{2p_1(0)}{\Delta(0)}\rceil$ rounds w.p. $\ge1-1/n^2$
-- statement:
--   Let $h\ge3$ and $2\le k\le n$, and let $i_0$ be a reference opinion ("opinion 1"). Let $c>0$ be a sufficiently small absolute constant and then $K>0$ a sufficiently large absolute constant depending on $c$ (the paper's $C$ in (⋆)). If the initial configuration is good, i.e. $p_{i_0}(0)>0$ and $\Delta(0)\ge K\sqrt{p_{i_0}(0)/\gamma(0)\cdot\ln n/n}$ with $\gamma(0)=\min\{h^2p_{i_0}(0),1\}$, then the phase succeeds within
--   $$T:=2\left\lceil\frac{32}{c\,\gamma(0)}\ln\Big(\frac{2p_{i_0}(0)}{\Delta(0)}\Big)\right\rceil$$
--   rounds with probability at least $1-1/n^2$: at some round $t\le T$, either $p_{i_0}(t)\ge3/5$, or $p_{i_0}(t)\ge2p_{i_0}(0)$, $\Delta(t)\ge p_{i_0}(t)/32$ and the configuration at round $t$ is good.
--
--   Iterating this lemma $O(\log n)$ times brings the plurality opinion to density $3/5$ (proof of Theorem 6.1).
--
--   **Formalization Note** "Sufficiently small $c$, then sufficiently large $K$ depending on $c$" is stated as: there is $c_0>0$ such that for every $c\in(0,c_0]$ there is $K_0>0$ such that for every $K\ge K_0$ the statement holds for all $n,k,h$, configurations and labels $i_0$. "Within $T$ rounds" is some round $t\le T$; $\lceil\cdot\rceil$ is the natural-number ceiling.
--
--   Differences from the source:
--   - reading: "Fix a sufficiently small absolute constant c > 0 and then a sufficiently large absolute constant C > 0 (depending on c)" (p.29) → ∃ c₀ > 0, ∀ c ∈ (0, c₀], ∃ K₀ > 0, ∀ K ≥ K₀, before n, k, h and the configuration; reason: the literal meaning of "sufficiently small/large"; it implies the existence of one admissible pair (c, C)
--   - encoding: opinion 1 of §6 (other opinions not sorted, p.28) → a label i₀ : Fin k; reason: §6 fixes only which opinion is opinion 1; same instances
--   - encoding: h-Majority as a sequence of random configurations (§2) → path law pathLaw h C₀ of the Markov kernel step h (product over nodes of Maj of h iid samples from p(C), uniform tie-breaking); reason: the §2 rule written as a kernel; the published Ionescu-Tulcea chain law gives the process
--   - encoding: nodes [n], opinions [k]; log n and ln n → Fin n, Fin k (0-based labels); Real.log; reason: Lean convention; the paper's log is natural (Lemma 6.9 and 7.2 proofs turn exp(−A log n) into n^{−A}); same instances
-- source:
--   d'Amore, Rybicki, Shimizu, Shiraga, Vacus, Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics, arXiv:2610.40562, Lemma 6.2, p.30 (definitions: §6, pp.28–29, (⋆); success of a phase, p.30; constants c, C, p.29)

import Mathlib
import Definitions.Def_HMajConsensus_IsGood

open MeasureTheory ProbabilityTheory

namespace HMajConsensus

/-- **Lemma 6.2** (d'Amore, Rybicki, Shimizu, Shiraga, Vacus, *Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics*, arXiv:2610.40562, §6.2, p.30): if the configuration `p(0)` is good, then the phase
succeeds within `T := 2⌈(32/(cγ(0))) ln(2p₁(0)/∆(0))⌉` rounds with probability at least
`1 − 1/n²`.

**Formalization Note** §6 fixes "a sufficiently small absolute constant `c > 0` and then a
sufficiently large absolute constant `C > 0` (depending on `c`)" (p.29): stated as
`∃ c₀ > 0, ∀ c ∈ (0, c₀], ∃ K₀ > 0, ∀ K ≥ K₀` (`K` is the paper's `C`), before `n, k, h` and the
configuration. "Opinion 1" is the label `i₀`; `h ≥ 3` (Theorem 6.1). "Within `T` rounds" is
some round `t ≤ T`. -/
theorem lemma_6_2_amplification_phase :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, 0 < c → c ≤ c₀ →
      ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ K : ℝ, K₀ ≤ K →
        ∀ (n k h : ℕ), 2 ≤ k → k ≤ n → 3 ≤ h → ∀ (C₀ : Config n k) (i₀ : Fin k),
          IsGood K h C₀ i₀ →
          1 - 1 / (n : ℝ) ^ 2 ≤ (pathLaw h C₀ {ω | ∃ t : ℕ,
            t ≤ 2 * ⌈32 / (c * growthRate h C₀ i₀) *
              Real.log (2 * density C₀ i₀ / gapMin C₀ i₀)⌉₊ ∧
            PhaseSucceeds K h C₀ (ω t) i₀}).toReal := by sorry

end HMajConsensus
