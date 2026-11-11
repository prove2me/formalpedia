-- Prove2me | Theorems.Thm_NonMarkovColorings_Main_proposition_5_6
-- name    : NonMarkovColorings.Main.proposition_5_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:10:39.222193+00:00
-- url     : https://prove2.me/theorems/1697254e-53ed-4137-9da9-01dde0d998c6
-- title:
--   Proposition 5.6 — tail of the potential-disagreement set: $\mathbb P[|\mathcal P|\ge\exp(\exp(C_{cp}^2))]\le\exp(-C_{cp}^2)$
-- statement:
--   In the setting of Theorem 5.4: for every $\delta>0$ there is $C_1$ such that for every integer $C_{cp}\ge C_1$ there is $\Delta_0$ such that for every graph $G$ of maximum degree $\Delta\ge\Delta_0$ and girth $\ge7$, every $k\ge(1+\delta)\Delta$, every fixed order of the bounding chain and all neighboring labelings $X_0,Y_0$, with $\vec\sigma$ uniform in $(V\times[k])^{T_{cp}}$, $T_{cp}=C_{cp}n$,
--   $$\mathbb P\big[|\mathcal P|\ge\exp(\exp(C_{cp}^2))\big]\le\exp(-C_{cp}^2),$$
--   where $\mathcal P=\bigcup_{t\le T_{cp}}\mathcal P_t$ is the potential-disagreement set of the bounding chain of $(X_0,Y_0,\vec\sigma)$. This controls condition (3) of $\mathrm{BC}$.
--
--   Differences from the source:
--   - reading: "in the setup of Theorem 5.4" (C_cp an integer and sufficiently large, Δ0 = Δ0(C_cp) enlarged, girth ≥ 7, k ≥ (1+δ)Δ, neighboring X0, Y0) → ∀ δ > 0, ∃ C1, ∀ C_cp ∈ ℕ with C_cp ≥ C1, ∃ Δ0, ∀ G (Δ ≥ Δ0, 7 ≤ egirth), k ≥ (1+δ)Δ, ∀ fixed order, ∀ X0, Y0 with |X0 ⊕ Y0| = 1; reason: the ≪-chain 1/Δ0 ≪ 1/C_cp ≪ δ read right to left (§1.3); the bounding chain's fixed order is arbitrary, so it is quantified universally
--   - encoding: colors [k] = {1, …, k} → Fin k = {0, …, k−1}; reason: Lean convention; a relabeling of colors, same instances
--   - encoding: girth ≥ 7 (a forest has infinite girth) → 7 ≤ G.egirth in ℕ∞ (⊤ for a forest); reason: Mathlib's SimpleGraph.girth is 0 for forests; egirth is the girth with the forest convention
--   - encoding: probability over the discrete-time dynamics → seqProb/seqExp: normalized count/sum over update sequences σ ∈ (V × Fin k)^T, X_t = run G X0 σ t; reason: the dynamics is driven by i.i.d. uniform updates (u, c); its law up to time T is the uniform law on update sequences
-- source:
--   Jain, Mizgerd, Vigoda, Sampling Colorings Close to the Maximum Degree: Non-Markovian Coupling and Local Uniformity, arXiv:2604.11938 (PDF of 2026-11-03, sha256 f3bf0cf0…), p. 34, Proposition 5.6

import Mathlib
import Definitions.Def_NonMarkovColorings_Main_GraphNotions
import Definitions.Def_NonMarkovColorings_Main_LabelingChain
import Definitions.Def_NonMarkovColorings_Main_BoundingChain

namespace NonMarkovColorings.Main

/-- Proposition 5.6, in the setup of Theorem 5.4 (`C_cp` an integer, sufficiently large, then
`Δ0` large in terms of `C_cp`): for neighboring `X0, Y0` and `σ` uniform in
`(V × [k])^{T_cp}`, `T_cp = C_cp n`, `P[|P| ≥ exp(exp(C_cp²))] ≤ exp(−C_cp²)`, for every fixed
order used by the bounding chain. -/
theorem proposition_5_6 (δ : ℝ) (hδ : 0 < δ) :
    ∃ C1 : ℕ, ∀ Ccp : ℕ, C1 ≤ Ccp → ∃ Δ0 : ℕ,
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (k : ℕ), Δ0 ≤ G.maxDegree → 7 ≤ G.egirth → (1 + δ) * (G.maxDegree : ℝ) ≤ k →
      ∀ (ob : VertexOrder V) (X0 Y0 : V → Fin k), (diffSet X0 Y0).card = 1 →
        seqProb V k (Tcp V Ccp) (fun σ =>
            Real.exp (Real.exp ((Ccp : ℝ) ^ 2)) ≤ ((bcPall G ob X0 Y0 σ).card : ℝ)) ≤
          Real.exp (-(Ccp : ℝ) ^ 2) := by sorry

end NonMarkovColorings.Main
