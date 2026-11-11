-- Prove2me | Theorems.Thm_NonMarkovColorings_Main_lemma_8_1
-- name    : NonMarkovColorings.Main.lemma_8_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:09:46.619109+00:00
-- url     : https://prove2.me/theorems/6b4ea7fb-d80e-460a-ac1c-bcb2095a308b
-- title:
--   Lemma 8.1 — identity coupling: $\mathbb E|X_T\oplus Y_T|\le\exp(2T/n)$ and a tail bound $\exp(-\sqrt\ell)$
-- statement:
--   For every $\delta>0$ and every $C\ge3$ there is $\Delta_0=\Delta_0(\delta,C)$ such that the following holds. Let $G$ be a graph on $n$ vertices with maximum degree $\Delta\ge\Delta_0$, let $k\ge(1+\delta)\Delta$, and let $X_0,Y_0\in\widehat\Omega$ be neighboring labelings evolving under the identity coupling (both chains use the same uniform update sequence). Then for any $T\ge Cn$:
--   (1) $\mathbb E|X_T\oplus Y_T|\le\exp(2T/n)$;
--   (2) for every $\ell\ge\exp(20T/n)$,
--   $$\mathbb E\big[|X_T\oplus Y_T|\,\mathbf 1(|X_T\oplus Y_T|>\ell^{2/3})\big]\le\exp(-\sqrt\ell).$$
--   These weak estimates control the Hamming distance on the failure events of the block argument of §8.
--
--   Differences from the source:
--   - encoding: colors [k] = {1, …, k} → Fin k = {0, …, k−1}; reason: Lean convention; a relabeling of colors, same instances
--   - encoding: probability over the discrete-time dynamics → seqProb/seqExp: normalized count/sum over update sequences σ ∈ (V × Fin k)^T, X_t = run G X0 σ t; reason: the dynamics is driven by i.i.d. uniform updates (u, c); its law up to time T is the uniform law on update sequences
--   - encoding: identity coupling → both chains run on the same σ uniform in (V × Fin k)^T; reason: the identity coupling uses the same update in both chains
-- source:
--   Jain, Mizgerd, Vigoda, Sampling Colorings Close to the Maximum Degree: Non-Markovian Coupling and Local Uniformity, arXiv:2604.11938 (PDF of 2026-11-03, sha256 f3bf0cf0…), p. 65, Lemma 8.1

import Mathlib
import Definitions.Def_NonMarkovColorings_Main_LabelingChain

namespace NonMarkovColorings.Main

/-- Lemma 8.1. For every `δ > 0` and `C ≥ 3` there is `Δ0` such that for every graph on `n`
vertices of maximum degree `Δ ≥ Δ0`, every `k ≥ (1 + δ)Δ`, and neighboring labelings `X0, Y0`
evolving under the identity coupling (both driven by the same uniform update sequence), for every
`T ≥ C n`: (1) `E|X_T ⊕ Y_T| ≤ exp(2T/n)`; (2) for every `ℓ ≥ exp(20T/n)`,
`E[|X_T ⊕ Y_T| 1(|X_T ⊕ Y_T| > ℓ^{2/3})] ≤ exp(−√ℓ)`. -/
theorem lemma_8_1 (δ : ℝ) (hδ : 0 < δ) (C : ℝ) (hC : 3 ≤ C) :
    ∃ Δ0 : ℕ,
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (k : ℕ), Δ0 ≤ G.maxDegree → (1 + δ) * (G.maxDegree : ℝ) ≤ k →
      ∀ (X0 Y0 : V → Fin k), (diffSet X0 Y0).card = 1 →
      ∀ T : ℕ, C * (Fintype.card V : ℝ) ≤ T →
        seqExp V k T (fun σ => ((diffSet (run G X0 σ T) (run G Y0 σ T)).card : ℝ)) ≤
            Real.exp (2 * (T : ℝ) / Fintype.card V) ∧
        ∀ ℓ : ℝ, Real.exp (20 * (T : ℝ) / Fintype.card V) ≤ ℓ →
          seqExp V k T (fun σ =>
              ((diffSet (run G X0 σ T) (run G Y0 σ T)).card : ℝ) *
                (if ℓ ^ ((2 : ℝ) / 3) < ((diffSet (run G X0 σ T) (run G Y0 σ T)).card : ℝ)
                  then 1 else 0)) ≤
            Real.exp (-Real.sqrt ℓ) := by sorry

end NonMarkovColorings.Main
