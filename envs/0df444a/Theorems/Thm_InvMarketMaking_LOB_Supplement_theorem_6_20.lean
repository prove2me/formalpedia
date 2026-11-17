-- Prove2me | Theorems.Thm_InvMarketMaking_LOB_Supplement_theorem_6_20
-- name    : InvMarketMaking.LOB.Supplement.theorem_6_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:35:27.077676+00:00
-- url     : https://prove2.me/theorems/838816e2-38bd-47ed-90fc-4e7b6b96b27d
-- title:
--   Theorem 6.20 — lower bound: on the hard instance (24), $|I_t|\le\alpha\le H$ forces $\mathbb E[R_T]\ge T/(720H)$ when $T\ge144H^2$
-- statement:
--   Consider the hard instance (24). In each round the seller's and the buyer's valuations are independent, each equal to $1/10$ or $9/10$ with probability $1/2$, i.i.d. across rounds. So $F(b)=\mathbb P(V^{\mathrm{sell}}\le b)$ and $S(a)=\mathbb P(V^{\mathrm{buy}}\ge a)$ are the step functions of (24). Let $\mathrm{OPT}=T\sup\{aS(a)-bF(b):b,a\in[0,1],\ b<a,\ F(b)=S(a)\}$ be the value of Program (3), and let $R_T=\mathrm{OPT}-\sum_{t=1}^T r_t$ be the regret, with $r_t=A_t\mathbb I(V^{\mathrm{buy}}_t\ge A_t)-B_t\mathbb I(V^{\mathrm{sell}}_t\le B_t)$.
--
--   Let $H\in\mathbb R$ and $T\in\mathbb N$ with $T\ge144H^2$. Consider any algorithm whose prices satisfy $0\le B_t<A_t\le1$ and are chosen from its own randomness, independent of the valuations, and the valuations of the previous rounds. Such an algorithm may know $F$ and $S$. Suppose it satisfies the per-round inventory constraint (2) for some threshold $\alpha\in\mathbb N_{>0}$ with $\alpha\le H$, that is, almost surely $|I_t|\le\alpha$ for every $t\in[T]$. Then
--   $$
--   \mathbb E[R_T]\ge\frac{T}{720H}.
--   $$
--   Keeping the inventory within $H$ costs regret of order $T/H$. In particular, any algorithm with $o(\sqrt T)$ per-round inventory must suffer $\omega(\sqrt T)$ regret, so the $\widetilde O(\sqrt T)$ guarantees of Section 6 are optimal up to logarithmic factors.
--
--   Differences from the source:
--   - reading: the hard instance is given by F and S in (24) → the joint law μ ⊗ μ with μ = ½δ_{1/10} + ½δ_{9/10} (hardLaw); reason: the proof uses that the seller's and the buyer's valuations are independent (p. 51: X^(0) with masses 1/4, 1/2, 1/4; p. 53: 'independence of the valuations')
--   - reading: 'every algorithm' → every pair of price processes with 0 ≤ B_t < A_t ≤ 1, measurable for 𝒢 ⊔ σ(past valuations) with 𝒢 independent of the valuations (IsNonanticipating); reason: p. 50 proves the bound even for agents that know F and S, 'stronger even than full feedback'; this class contains every feedback model of the paper
--   - reading: 'satisfies the per-round inventory constraint for α ≤ H' → ∃ α ∈ ℕ with 1 ≤ α ≤ H and, almost surely, |I_t| ≤ α for every t ∈ [T]; reason: Eq. (2) takes α ∈ ℕ_{>0}; the proof uses E|I_k − I_j| ≤ 2H and I_T ≥ −H
--   - encoding: E[R_T] with R_T = OPT − Σ_t r_t, and OPT the maximum of Program (3) → OPT hardLaw T − ∫ Σ_{t∈[T]} r_t dP, with OPT = T · sSup of the feasible values (form (6)); reason: the sum is bounded and measurable, so integrable; the supremum is attained (2/5 at (1/10, 9/10))
--   - encoding: valuation pairs i.i.d. from V_hard → measurable sequences indexed by ℕ, mutually independent, each with law hardLaw (IsValuationModel); index 0 and indices beyond T unused; reason: every event involves rounds 1, …, T only
--   - reading: S(a) = E[I(V^buy ≥ a)] = 1 − F_buy(a) (p. 16) → S(a) = P(V^buy ≥ a) (the published buySurv); reason: the two expressions differ exactly at atoms of V^buy; the trade probability E[I(V^buy ≥ a)] is what Program (3), the model and every proof use; Eq. (24) is also P(V^buy ≥ a)
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Theorem 6.20, p. 53 (hard instance Eq. (24), p. 50; Program (3), p. 16; Eq. (2), p. 16)

import Mathlib
import Definitions.Def_InvMarketMaking_LOB_J
import Definitions.Def_InvMarketMaking_LOB_IsRoundModel
import Definitions.Def_InvMarketMaking_LOB_Supplement_ppImbalance
import Definitions.Def_InvMarketMaking_LOB_Supplement_hardLaw
import Definitions.Def_InvMarketMaking_LOB_Supplement_IsNonanticipating

open MeasureTheory ProbabilityTheory

namespace InvMarketMaking.LOB.Supplement

/-- **Theorem 6.20** (Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market
Making Under Inventory Constraints, arXiv:2610.24562v1, p. 53). Let `T ≥ 144 H²`. Then every algorithm
that satisfies the per-round inventory constraint for `α ≤ H` suffers expected regret
`E[R_T] ≥ T/(720 H)`, on the hard instance (24).

**Formalization Note** (i) The valuation pairs are i.i.d. with the hard law (24): seller and buyer
independent within a round, each `½ δ_{1/10} + ½ δ_{9/10}` (`hardLaw`). (ii) "Every algorithm" is every
pair of price processes with `0 ≤ B_t < A_t ≤ 1` chosen from the algorithm's own randomness
(independent of the valuations) and the past valuations (`IsNonanticipating`); this includes algorithms
that know `F` and `S` (p. 50). (iii) The per-round inventory constraint (Eq. (2), p. 16) holds almost
surely with a threshold `α ∈ ℕ_{>0}` such that `α ≤ H`. (iv) `R_T = OPT − Σ_{t=1}^T r_t` is the regret
against Program (3) (p. 17), not the surrogate regret, and `E[R_T] = OPT − E[Σ_{t ≤ T} r_t]`; `OPT`
is stated generically and evaluated at the hard law (it equals `2T/5`, p. 50). -/
theorem theorem_6_20 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : Market Ω) (hM : IsValuationModel P hardLaw M)
    (H : ℝ) (T : ℕ) (hT : 144 * H ^ 2 ≤ (T : ℝ))
    (bid ask : ℕ → Ω → ℝ) (halg : IsNonanticipating P M bid ask T)
    (hinv : ∃ α : ℕ, 1 ≤ α ∧ (α : ℝ) ≤ H ∧
      ∀ᵐ ω ∂P, ∀ t ∈ Finset.Icc 1 T, |ppImbalance M bid ask t ω| ≤ α) :
    (T : ℝ) / (720 * H) ≤
      OPT hardLaw T - ∫ ω, (∑ t ∈ Finset.Icc 1 T, ppReward M bid ask t ω) ∂P := by sorry

end InvMarketMaking.LOB.Supplement
