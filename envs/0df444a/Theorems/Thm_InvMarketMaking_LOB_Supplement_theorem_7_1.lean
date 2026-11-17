-- Prove2me | Theorems.Thm_InvMarketMaking_LOB_Supplement_theorem_7_1
-- name    : InvMarketMaking.LOB.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:35:57.04299+00:00
-- url     : https://prove2.me/theorems/dbab173e-85f2-4038-95b7-25c4a296d44d
-- title:
--   Theorem 7.1 (corrected: $\mathcal A$'s two bounds on one event) — Algorithm 6 gives $R^J_T\le R^J_{\mathcal A}+2I_{\mathcal A}$, $|I_T|=0$, $|I_t|\le I_{\mathcal A}$
-- statement:
--   In the market-making model of Section 3, the valuation pairs are i.i.d. from a joint law $\mathcal V$ on $[0,1]^2$ with $\mathbb P(V^{\mathrm{buy}}=1)=\mathbb P(V^{\mathrm{sell}}=0)=0$. Let $T\ge1$ and $\delta\in(0,1)$. Let $\mathcal A$ be an algorithm, run for horizon $T$, with prices in $[0,1]$. Let $R^J_{\mathcal A}\in\mathbb R$ and $I_{\mathcal A}\in\mathbb N$ be such that, with probability at least $1-\delta$, $\mathcal A$'s surrogate regret satisfies $R^J_t\le R^J_{\mathcal A}$ and its imbalance satisfies $|I_t|\le I_{\mathcal A}$ for every $t\in[T]$, both on the same event. Then Algorithm 6 instantiated with $\mathcal A$ attains, with probability at least $1-\delta$,
--   $$
--   R^J_T\le R^J_{\mathcal A}+2I_{\mathcal A},\qquad |I_T|=0,\qquad |I_t|\le I_{\mathcal A}\ \ \forall t\in[T].
--   $$
--   The wrapper converts any per-round inventory guarantee into exact global inventory balance (Eq. (1)) at an additive regret cost of $2I_{\mathcal A}$. Combined with Theorems 5.13 and 6.18, it yields algorithms that satisfy both inventory constraints.
--
--   Differences from the source:
--   - correction: A's regret and per-round imbalance 'are upper bounded by R^J_A, I_A with probability at least 1 − δ, respectively' (two events, each of probability ≥ 1 − δ) → one event of probability ≥ 1 − δ on which R^J_t(A) ≤ R^J_A and |I_t(A)| ≤ I_A for every t ∈ [T]; reason: with two separate events the conclusion fails: T = 1, I_A = 0, δ = 1/2, V = δ_{(1/4, 3/4)} (so J* = 1/2), A posts (0, 3/4) on heads and (0, 1) on tails of an independent fair coin, R^J_A = 0; then P(R^J_1 ≤ 0) = P(heads) = 1/2 and P(|I_1| ≤ 0) = P(tails) = 1/2, but Algorithm 6 equals A (T − I_A = 1) and its conclusion needs both on the same ω, which has probability 0 < 1/2; the paper's guarantees (Theorems 5.13, 6.18, 6.19) all have the one-event form
--   - reading: A's '(surrogate) regret … upper bounded by R^J_A' → R^J_t(A) ≤ R^J_A for every t ∈ [T] (on the event); reason: the proof bounds the regret of A up to round T − I_A by R^J_A, which a bound at the horizon T alone does not give; the paper's guarantees bound R^J_t at every t
--   - generalization: A is an algorithm for the online market making problem (0 ≤ B_t < A_t ≤ 1, chosen online) → A is any pair of price processes with values in [0, 1] on rounds 1, …, T; no adaptivity and no B_t < A_t is assumed; reason: the argument is pathwise and uses only that A's prices lie in [0, 1]; every algorithm is such a pair of processes, so the statement specializes to the source
--   - encoding: I_A, possibly non-integer (footnote 6: assume an integer, else use ⌊I_A⌋) → I_A ∈ ℕ; reason: footnote 6 reduces to the integer case
--   - encoding: valuation pairs i.i.d. from V → measurable sequences indexed by ℕ, mutually independent, each with law V (IsValuationModel); index 0 and indices beyond T unused; reason: every event involves rounds 1, …, T only
--   - reading: S(a) = E[I(V^buy ≥ a)] = 1 − F_buy(a) (p. 16) → S(a) = P(V^buy ≥ a) (the published buySurv); reason: the two expressions differ exactly at atoms of V^buy; the trade probability E[I(V^buy ≥ a)] is what Program (3), the model and every proof use; Eq. (24) is also P(V^buy ≥ a)
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Theorem 7.1, p. 55 (Algorithm 6, p. 55)

import Mathlib
import Definitions.Def_InvMarketMaking_LOB_IsValuationLaw
import Definitions.Def_InvMarketMaking_LOB_J
import Definitions.Def_InvMarketMaking_LOB_surrogateRegret
import Definitions.Def_InvMarketMaking_LOB_Supplement_ppImbalance
import Definitions.Def_InvMarketMaking_LOB_Supplement_globalBalance

open MeasureTheory ProbabilityTheory

namespace InvMarketMaking.LOB.Supplement

/-- **Theorem 7.1** (Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market
Making Under Inventory Constraints, arXiv:2610.24562v1, p. 55). Let `δ ∈ (0, 1)` and let `A` be an
algorithm for the online market making problem whose (surrogate) regret and per-round imbalance are
upper bounded by `R^J_A`, `I_A` with probability at least `1 − δ`. Then Algorithm 6 instantiated with
`A` attains with probability at least `1 − δ`: `R^J_T ≤ R^J_A + 2 I_A`, `|I_T| = 0`, and
`|I_t| ≤ I_A` for all `t ∈ [T]`.

**Formalization Note** (i) The valuation pairs are i.i.d. from any `V` satisfying the standing
assumptions (Sec. 3, p. 14). (ii) `A` is given by its price processes `(B^A_t, A^A_t)` with values in
`[0, 1]`, run for horizon `T`; no adaptivity condition and no `B^A_t < A^A_t` is needed, since the
argument is pathwise. (iii) The hypothesis is one event of probability at least `1 − δ` on which `A`'s
regret and imbalance bounds hold at every `t ∈ [T]` (the format of the paper's guarantees, Theorems
5.13, 6.18, 6.19). (iv) `R^J_A ∈ ℝ` and `I_A ∈ ℕ` are deterministic (footnote 6: `I_A` an integer).
(v) `R^J_t = t·J* − Σ_{τ ≤ t} r_τ`; the wrapper's pairs `(1, 1)` and `(0, 0)` are allowed (p. 55). -/
theorem theorem_7_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Measure (ℝ × ℝ)) [IsProbabilityMeasure V] (hV : IsValuationLaw V)
    (M : Market Ω) (hM : IsValuationModel P V M)
    (T : ℕ) (hT : 1 ≤ T) (δ : ℝ) (hδ : δ ∈ Set.Ioo 0 1)
    (bidA askA : ℕ → Ω → ℝ)
    (hrange : ∀ t ∈ Finset.Icc 1 T, ∀ ω,
      bidA t ω ∈ Set.Icc (0 : ℝ) 1 ∧ askA t ω ∈ Set.Icc (0 : ℝ) 1)
    (RA : ℝ) (IA : ℕ)
    (hA : ENNReal.ofReal (1 - δ) ≤ P {ω | ∀ t ∈ Finset.Icc 1 T,
      surrogateRegret V (fun τ => ppReward M bidA askA τ ω) t ≤ RA ∧
      |ppImbalance M bidA askA t ω| ≤ IA}) :
    ENNReal.ofReal (1 - δ) ≤ P {ω |
      surrogateRegret V
          (fun τ => ppReward M (wrapBid T IA bidA askA M) (wrapAsk T IA bidA askA M) τ ω) T ≤
        RA + 2 * IA ∧
      |ppImbalance M (wrapBid T IA bidA askA M) (wrapAsk T IA bidA askA M) T ω| = 0 ∧
      ∀ t ∈ Finset.Icc 1 T,
        |ppImbalance M (wrapBid T IA bidA askA M) (wrapAsk T IA bidA askA M) t ω| ≤ IA} := by sorry

end InvMarketMaking.LOB.Supplement
