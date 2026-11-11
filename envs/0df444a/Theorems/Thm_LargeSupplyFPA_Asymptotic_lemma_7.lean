-- Prove2me | Theorems.Thm_LargeSupplyFPA_Asymptotic_lemma_7
-- name    : LargeSupplyFPA.Asymptotic.lemma_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:03:52.317935+00:00
-- url     : https://prove2.me/theorems/1702f17b-bf9e-42c2-b2b9-a0010b375d55
-- title:
--   Lemma 7 — smoothing atoms preserves interim allocations: $x_i(b)=\tilde x_i(\tilde b)$, and $x_i(b)=\mathbb E[\tilde x_i(\tilde b)]$ at atoms
-- statement:
--   Consider a $k$-unit first-price auction with $n$ agents, value laws $V$ and strategy profile $E$. Let $\omega>0$ and weights $s_p>0$ ($p\in\mathcal P$, the atoms of the marginal bid distributions) with $\sum_{p\in\mathcal P}s_p<\omega$. Let $\tilde x_i$ be the interim allocation when every agent's bid $b$ is replaced by the smoothed bid $\tilde b$ of (37)–(38). Then for every agent $i$ and every bid $b\ge0$:
--
--   (i) if $b\notin\mathcal P$, then $x_i(b)=\tilde x_i\big(b+\sum_{p\in\mathcal P,\,p<b}s_p\big)$;
--
--   (ii) if $b\in\mathcal P$, then
--   $$x_i(b)=\int_0^1\tilde x_i\Big(b+\sum_{p\in\mathcal P,\,p<b}s_p+s_b\,u\Big)\,du=\mathbb E\big[\tilde x_i(\tilde b)\big].$$
--
--   This is the key step of Theorem 3(c). The cumulative shifts keep the order of bids, and the uniform jitter at an atom reproduces uniform tie-breaking.
--
--   Differences from the source:
--   - encoding: a strategy is a map E_i : V_i → Δ(ℝ≥0) from values to bid distributions → a Markov kernel E i : Kernel ℝ ℝ with E i v ((−∞, 0)) = 0 for every v; reason: measurability in v is what makes the marginal bid distribution ∫ E_{i,v} dV_i defined; a law on ℝ with no mass below 0 is a law on ℝ≥0
--   - generalization: the construction starts from an ϵ-approximate equilibrium E → any strategy profile E; reason: Lemma 7 concerns allocation probabilities only and its proof uses no equilibrium property; the printed setting is the special case
--   - encoding: x_i(b_i) = E[x̃_i(b̃_i)] for the random bid b̃_i of (38) → x_i(b) = ∫_{[0,1]} x̃_i(b + shift(b) + s_b u) du; reason: the expectation over U ∼ U[0,1] written as a Lebesgue integral
--   - encoding: bid b_i ∈ ℝ≥0; weights s_p ∈ ℝ>0 for p ∈ P with ∑ s_p < ω → b : ℝ with 0 ≤ b; s : ℝ → ℝ positive on P, summable over P, ∑' < ω; reason: Lean types; values of s off P are irrelevant
-- source:
--   Hartline, Shah, vonAllmen, Robust Analysis of First-Price Auctions with Large Supply, STOC 2027 submission (manuscript of November 3, 2026, sha256 2ad8363b…), p. 30, Lemma 7 (construction (37)–(38) p. 29; proof pp. 31–32)

import Mathlib
import Definitions.Def_LargeSupplyFPA_Asymptotic_Model
import Definitions.Def_LargeSupplyFPA_Asymptotic_Smoothing

open MeasureTheory ProbabilityTheory

namespace LargeSupplyFPA.Asymptotic

theorem lemma_7 {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ)
    (hV : IsValueProfile V) (hE : IsStrategyProfile E)
    (ω : ℝ) (hω : 0 < ω) (s : ℝ → ℝ) (hs : IsSmoothingWeights V E ω s)
    (i : Fin n) (b : ℝ) (hb : 0 ≤ b) :
    (b ∉ atomSet V E →
      alloc k V E i b = smoothedAlloc k V E s i (b + atomShift V E s b)) ∧
    (b ∈ atomSet V E →
      alloc k V E i b =
        ∫ u in Set.Icc (0 : ℝ) 1, smoothedAlloc k V E s i (b + atomShift V E s b + s b * u)) := by sorry

end LargeSupplyFPA.Asymptotic
