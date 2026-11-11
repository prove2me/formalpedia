-- Prove2me | Theorems.Thm_NonMarkovColorings_Main_proposition_8_2
-- name    : NonMarkovColorings.Main.proposition_8_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:09:44.852504+00:00
-- url     : https://prove2.me/theorems/8535926e-643b-41c3-b2e5-0c1f21f3cb5c
-- title:
--   Proposition 8.2 — contraction over $T_{blk}=C_{blk}n\log\Delta$ steps: $\mathbb E|X_{T_{blk}}\oplus Y_{T_{blk}}|\le\Delta^{-1}$
-- statement:
--   For every $\delta>0$ there exist constants $\Delta_0(\delta)$ and $C_{blk}(\delta)$ such that for every graph $G$ on $n$ vertices of maximum degree $\Delta\ge\Delta_0$ and girth at least $7$, every $k\ge(1+\delta)\Delta$, and all neighboring labelings with $X_0\oplus Y_0=\{z^*\}$, setting $T_{blk}=C_{blk}n\log\Delta$, there is a $T_{blk}$-step coupling of the Metropolis dynamics from $(X_0,Y_0)$ with
--   $$\mathbb E\big|X_{T_{blk}}\oplus Y_{T_{blk}}\big|\le\Delta^{-1}.$$
--   With path coupling this gives Theorem 1.3 directly.
--
--   **Formalization Note.** The coupling is a joint law $q$ of $(X_{T_{blk}},Y_{T_{blk}})$ whose marginals are the $T_{blk}$-step laws of the Metropolis rule on $\widehat\Omega$ from $X_0$ and from $Y_0$ (`MarkovMixing.IsCoupling` of `rowDist (labelingChain G k)`).
--
--   Differences from the source:
--   - reading: T_blk = C_blk n log Δ (not an integer in general) → T_blk = ⌈C_blk n log Δ⌉₊; reason: a number of steps is an integer; rounding up is the standard reading
--   - reading: a T_blk-step coupling of the dynamics → a coupling q of the two T_blk-step laws on Ω̂; reason: any coupling of two chains induces one of their endpoint laws and conversely every endpoint coupling extends to a coupling of the chains
--   - reading: constant C_blk(δ) → 0 < C_blk; reason: C_blk is a positive step-count constant
--   - encoding: colors [k] = {1, …, k} → Fin k = {0, …, k−1}; reason: Lean convention; a relabeling of colors, same instances
--   - encoding: girth ≥ 7 (a forest has infinite girth) → 7 ≤ G.egirth in ℕ∞ (⊤ for a forest); reason: Mathlib's SimpleGraph.girth is 0 for forests; egirth is the girth with the forest convention
-- source:
--   Jain, Mizgerd, Vigoda, Sampling Colorings Close to the Maximum Degree: Non-Markovian Coupling and Local Uniformity, arXiv:2604.11938 (PDF of 2026-11-03, sha256 f3bf0cf0…), p. 65, Proposition 8.2

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_NonMarkovColorings_Main_LabelingChain

namespace NonMarkovColorings.Main

/-- Proposition 8.2. For every `δ > 0` there are `Δ0` and `C_blk > 0` such that for every graph
on `n` vertices of maximum degree `Δ ≥ Δ0` and girth `≥ 7`, every `k ≥ (1 + δ)Δ`, and neighboring
labelings `X0 ⊕ Y0 = {z*}`, with `T_blk = ⌈C_blk n log Δ⌉`, there is a coupling of the
`T_blk`-step laws of the Metropolis dynamics on all labelings from `X0` and from `Y0` under which
`E|X_{T_blk} ⊕ Y_{T_blk}| ≤ Δ^{−1}`. -/
theorem proposition_8_2 (δ : ℝ) (hδ : 0 < δ) :
    ∃ Δ0 : ℕ, ∃ Cblk : ℝ, 0 < Cblk ∧
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (k : ℕ), Δ0 ≤ G.maxDegree → 7 ≤ G.egirth → (1 + δ) * (G.maxDegree : ℝ) ≤ k →
      ∀ (X0 Y0 : V → Fin k) (z : V), diffSet X0 Y0 = {z} →
        ∃ q : (V → Fin k) × (V → Fin k) → ℝ,
          MarkovMixing.IsCoupling
            (MarkovMixing.rowDist (labelingChain G k)
              ⌈Cblk * (Fintype.card V : ℝ) * Real.log (G.maxDegree : ℝ)⌉₊ X0)
            (MarkovMixing.rowDist (labelingChain G k)
              ⌈Cblk * (Fintype.card V : ℝ) * Real.log (G.maxDegree : ℝ)⌉₊ Y0) q ∧
          ∑ x, q x * ((diffSet x.1 x.2).card : ℝ) ≤ ((G.maxDegree : ℝ))⁻¹ := by sorry

end NonMarkovColorings.Main
