-- Prove2me | Theorems.Thm_NonMarkovColorings_Main_theorem_5_4
-- name    : NonMarkovColorings.Main.theorem_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:10:51.102601+00:00
-- url     : https://prove2.me/theorems/ee2ece43-d641-4e0a-808c-86564d9256cc
-- title:
--   Theorem 5.4 — one-block contraction: a $T_{cp}=C_{cp}n$ step coupling with $\mathbb E[|X_{T_{cp}}\oplus Y_{T_{cp}}|\,\mathbf 1\{\mathrm{LU}\}]\le 1/3$
-- statement:
--   For every $\delta>0$ there exist constants $1/\Delta_0\ll\varepsilon\ll1/C_{cp}\ll\delta$ such that the following holds. Let $G=(V,E)$ be a graph on $n$ vertices of maximum degree $\Delta\ge\Delta_0$ and girth at least $7$, let $k\ge(1+\delta)\Delta$, let $X_0,Y_0\in\widehat\Omega$ be neighboring labelings with unique disagreement at $z^*$, and set $T_{cp}=C_{cp}n$. Then there is a $T_{cp}$-step coupling of the Metropolis dynamics such that
--   $$\mathbb E\big[|X_{T_{cp}}\oplus Y_{T_{cp}}|\cdot\mathbf 1\{\mathrm{LU}(X_0,\vec\sigma,\varepsilon,z^*)\}\big]\le\frac13 .$$
--   The $\ll$-chain is read right to left (§1.3): there is $C_1(\delta)$ such that for every integer $C_{cp}\ge C_1$ there is $\varepsilon>0$, and then $\Delta_0$. This is the formal version of Theorem 1.6: from a burned-in pair the expected Hamming distance contracts by a factor $3$ in $O(n)$ steps.
--
--   **Formalization Note.** A $T_{cp}$-step coupling is a law $\mu$ on pairs $(\vec\sigma,\vec\sigma')$ with both marginals uniform (`IsSeqCoupling`); $X$ runs on $\vec\sigma$ from $X_0$, $Y$ on $\vec\sigma'$ from $Y_0$, and LU is evaluated on $(X_0,\vec\sigma)$. Since $\mathbf 1\{\mathrm{LU}\}$ only decreases when $\varepsilon$ decreases, the existence of one $\varepsilon$ gives every smaller one as well.
--
--   Differences from the source:
--   - reading: constants 1/Δ0 ≪ ε ≪ 1/C_cp ≪ δ → ∃ C1, ∀ C_cp ∈ ℕ with C_cp ≥ C1, ∃ ε > 0, ∃ Δ0; reason: §1.3: a ≪-chain is read right to left; ∀ C_cp ≥ C1 is stronger than ∃ C_cp; C_cp is an integer (p. 34)
--   - reading: a T_cp-step coupling of the Metropolis dynamics → a joint law μ of (σ, σ') ∈ ((V × Fin k)^{T_cp})² with uniform marginals; reason: the paper's coupling is σ' = F(σ); any coupling of the two chains' update sequences is allowed, as the statement says "there exists a coupling"
--   - encoding: colors [k] = {1, …, k} → Fin k = {0, …, k−1}; reason: Lean convention; a relabeling of colors, same instances
--   - encoding: girth ≥ 7 (a forest has infinite girth) → 7 ≤ G.egirth in ℕ∞ (⊤ for a forest); reason: Mathlib's SimpleGraph.girth is 0 for forests; egirth is the girth with the forest convention
-- source:
--   Jain, Mizgerd, Vigoda, Sampling Colorings Close to the Maximum Degree: Non-Markovian Coupling and Local Uniformity, arXiv:2604.11938 (PDF of 2026-11-03, sha256 f3bf0cf0…), p. 34, Theorem 5.4

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_NonMarkovColorings_Main_LabelingChain
import Definitions.Def_NonMarkovColorings_Main_LocalUniformity
import Definitions.Def_NonMarkovColorings_Main_BoundingChain

namespace NonMarkovColorings.Main

open scoped Classical in
/-- Theorem 5.4. For every `δ > 0` there are constants `1/Δ0 ≪ ε ≪ 1/C_cp ≪ δ` (read right to
left: `C_cp ≥ C1(δ)`, then `ε > 0` small in terms of `C_cp`, then `Δ0` large) such that for every
graph on `n` vertices of maximum degree `Δ ≥ Δ0` and girth `≥ 7`, every `k ≥ (1 + δ)Δ`, and all
neighboring labelings `X0, Y0` with `X0 ⊕ Y0 = {z*}`, there is a `T_cp`-step coupling
(`T_cp = C_cp n`) — a joint law of `(σ, σ')` with uniform marginals, `X` run on `σ` from `X0`
and `Y` on `σ'` from `Y0` — with `E[|X_{T_cp} ⊕ Y_{T_cp}| · 1{LU(X0, σ, ε, z*)}] ≤ 1/3`. -/
theorem theorem_5_4 (δ : ℝ) (hδ : 0 < δ) :
    ∃ C1 : ℕ, ∀ Ccp : ℕ, C1 ≤ Ccp → ∃ ε : ℝ, 0 < ε ∧ ∃ Δ0 : ℕ,
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (k : ℕ), Δ0 ≤ G.maxDegree → 7 ≤ G.egirth → (1 + δ) * (G.maxDegree : ℝ) ≤ k →
      ∀ (X0 Y0 : V → Fin k) (z : V), diffSet X0 Y0 = {z} →
        ∃ μ : UpdSeq V k (Tcp V Ccp) × UpdSeq V k (Tcp V Ccp) → ℝ,
          IsSeqCoupling V k (Tcp V Ccp) μ ∧
          ∑ q, μ q * ((diffSet (run G X0 q.1 (Tcp V Ccp)) (run G Y0 q.2 (Tcp V Ccp))).card : ℝ) *
              (if LU G ε z X0 q.1 then 1 else 0) ≤ 1 / 3 := by sorry

end NonMarkovColorings.Main
