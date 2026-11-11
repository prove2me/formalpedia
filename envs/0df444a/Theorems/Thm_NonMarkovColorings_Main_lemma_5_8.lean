-- Prove2me | Theorems.Thm_NonMarkovColorings_Main_lemma_5_8
-- name    : NonMarkovColorings.Main.lemma_5_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:10:51.330099+00:00
-- url     : https://prove2.me/theorems/816739ea-d89b-4b69-a62e-a332cdf45bfb
-- title:
--   Lemma 5.8 — the bounding chain is well behaved with probability at least $1-2\exp(-C_{cp}^2)$
-- statement:
--   In the setting of Theorem 5.4 (quantifiers as in Proposition 5.6): for neighboring labelings $X_0,Y_0\in\widehat\Omega$,
--   $$\mathbb P_{\vec\sigma}\big[\mathrm{BC}(X_0,Y_0,\vec\sigma)\big]\ge 1-2\exp(-C_{cp}^2),$$
--   with $\vec\sigma$ uniform in $(V\times[k])^{T_{cp}}$. Here girth $\ge7$ is used to rule out short cycles through the potential-disagreement set.
--
--   Differences from the source:
--   - reading: "in the setup of Theorem 5.4" (C_cp an integer and sufficiently large, Δ0 = Δ0(C_cp) enlarged, girth ≥ 7, k ≥ (1+δ)Δ, neighboring X0, Y0) → ∀ δ > 0, ∃ C1, ∀ C_cp ∈ ℕ with C_cp ≥ C1, ∃ Δ0, ∀ G (Δ ≥ Δ0, 7 ≤ egirth), k ≥ (1+δ)Δ, ∀ fixed order, ∀ X0, Y0 with |X0 ⊕ Y0| = 1; reason: the ≪-chain 1/Δ0 ≪ 1/C_cp ≪ δ read right to left (§1.3); the bounding chain's fixed order is arbitrary, so it is quantified universally
--   - encoding: colors [k] = {1, …, k} → Fin k = {0, …, k−1}; reason: Lean convention; a relabeling of colors, same instances
--   - encoding: girth ≥ 7 (a forest has infinite girth) → 7 ≤ G.egirth in ℕ∞ (⊤ for a forest); reason: Mathlib's SimpleGraph.girth is 0 for forests; egirth is the girth with the forest convention
--   - encoding: probability over the discrete-time dynamics → seqProb/seqExp: normalized count/sum over update sequences σ ∈ (V × Fin k)^T, X_t = run G X0 σ t; reason: the dynamics is driven by i.i.d. uniform updates (u, c); its law up to time T is the uniform law on update sequences
-- source:
--   Jain, Mizgerd, Vigoda, Sampling Colorings Close to the Maximum Degree: Non-Markovian Coupling and Local Uniformity, arXiv:2604.11938 (PDF of 2026-11-03, sha256 f3bf0cf0…), p. 36, Lemma 5.8

import Mathlib
import Definitions.Def_NonMarkovColorings_Main_GraphNotions
import Definitions.Def_NonMarkovColorings_Main_LabelingChain
import Definitions.Def_NonMarkovColorings_Main_BoundingChain

namespace NonMarkovColorings.Main

/-- Lemma 5.8, in the setup of Theorem 5.4: for neighboring labelings `X0, Y0`,
`P_σ[BC(X0, Y0, σ)] ≥ 1 − 2 exp(−C_cp²)` over `σ` uniform in `(V × [k])^{T_cp}`, for every fixed
order used by the bounding chain. -/
theorem lemma_5_8 (δ : ℝ) (hδ : 0 < δ) :
    ∃ C1 : ℕ, ∀ Ccp : ℕ, C1 ≤ Ccp → ∃ Δ0 : ℕ,
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (k : ℕ), Δ0 ≤ G.maxDegree → 7 ≤ G.egirth → (1 + δ) * (G.maxDegree : ℝ) ≤ k →
      ∀ (ob : VertexOrder V) (X0 Y0 : V → Fin k), (diffSet X0 Y0).card = 1 →
        1 - 2 * Real.exp (-(Ccp : ℝ) ^ 2) ≤
          seqProb V k (Tcp V Ccp) (fun σ => BC G ob Ccp X0 Y0 σ) := by sorry

end NonMarkovColorings.Main
