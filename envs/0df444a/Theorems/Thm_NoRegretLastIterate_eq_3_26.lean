-- Prove2me | Theorems.Thm_NoRegretLastIterate_eq_3_26
-- name    : NoRegretLastIterate.eq_3_26
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:33:54.252893+00:00
-- url     : https://prove2.me/theorems/3cb67f2a-65b1-4704-ab16-4cd07102364c
-- title:
--   Eq. (3.26) — under $Q_t\to q^*$ a.s., $\sqrt t(\widehat Q_t-q^*)$ exceeds $\pm\beta$ with probability bounded below (corrected: positivity, no erfc constant)
-- statement:
--   Assume the setting of Theorem 3.4: a competitive game $(G,H)$ with Nash equilibrium $(p^*,q^*)$, both players using monotonic mean-based strategies with an optimal no-regret rate, and $(\Omega,\mu,I,J)$ carrying the realization-based play. If player 2's mixed strategies satisfy $Q_t\to q^*$ almost surely, then for every $\beta>0$
--   $$
--   \liminf_{t\to\infty}\Pr\big(\sqrt t(\widehat Q_t-q^*)\ge\beta\big)>0\qquad\text{and}\qquad\liminf_{t\to\infty}\Pr\big(\sqrt t(\widehat Q_t-q^*)\le-\beta\big)>0,
--   $$
--   where $\widehat Q_t=\frac1t\sum_{s=1}^tJ_s$ is the empirical frequency of player 2's actions.
--
--   Almost sure convergence of player 2's mixed strategy does not stop his realized frequency from fluctuating at order $1/\sqrt t$ around $q^*$, in both directions. Combined with Eq. (3.20), these fluctuations push player 1 a constant distance away from $p^*$ with probability bounded below, which contradicts $P_t\to p^*$.
--
--   **Formalization Note** "$\liminf>0$" is written as: some $\varepsilon>0$ bounds the probability from below for all large $t$.
--
--   Differences from the source:
--   - correction: lim_{k→∞} P(√t_k(Q̂_{t_k} − q∗) ≥ β) ≥ erfc((β + C)/γ(q∗)) > 0 → lim inf_{t→∞} P(√t(Q̂_t − q∗) ≥ β) > 0; reason: C is the constant of Lemma 3.7, which does not exist as printed (pointwise bound false), and step (ii) of the display on p.19 bounds a Gaussian tail P(N ≥ x/√γ) below by erfc(x/γ), which tends to 1 as x → 0 while the probability is below 1/2; positivity is what the proof of Theorem 3.4 uses
--   - generalization: upper tail only → adds lim inf_t P(√t(Q̂_t − q∗) ≤ −β) > 0; reason: needed for rounds where f_t is non-increasing (the mirror branch of Eq. (3.20)); the upper-tail clause is unchanged
--   - encoding: limit along a deterministic subsequence t_k → lim inf over all t, as ∃ ε > 0, eventually ε ≤ P(…); reason: a positive lim inf over all t is equivalent to a positive lim inf along every deterministic subsequence
--   - reading: hypotheses of (3.26): the setting of Theorem 3.4 and "if Q_t → q∗ a.s." (p.17) → hypotheses of the goal plus Q_t → q∗ almost surely; reason: (3.26) is derived inside the proof of Theorem 3.4 under these assumptions
--   - encoding: uniform no-regret rate (r, c) for a finite c: lim sup_T max_J T^{−r} Reg_T(J) ≤ c → ∃ c, for all large T and all J, Reg_T(J) ≤ c·T^r; reason: equivalent, since the maximum over {0,1}^T is finite; avoids a real-valued limsup
--   - encoding: (p∗, q∗) a Nash equilibrium in mixed strategies; actions 0, 1 → published RankOneBimatrix.BinSearch.IsNE on the probability vectors (1 − p, p), (1 − q, q); actions Fin 2; reason: Lean convention and published vocabulary; same instances
--   - encoding: rounds t = 1, 2, …; f_t applied to (J)^{t−1} → Lean rounds n = t − 1 from 0; F n applied to the first n actions; reason: Lean convention; same instances
-- source:
--   Muthukumar, Phade, Sahai, On the Impossibility of Convergence of Mixed Strategies with Optimal No-Regret Learning, arXiv:2012.02125v3, Eq. (3.26), p.19

import Mathlib
import Definitions.Def_RankOneBimatrix_BinSearch_Game
import Definitions.Def_NoRegretLastIterate_Game
import Definitions.Def_NoRegretLastIterate_Strategy
import Definitions.Def_NoRegretLastIterate_MeanBased
import Definitions.Def_NoRegretLastIterate_Play

open MeasureTheory Matrix Filter Topology

namespace NoRegretLastIterate

/-- Muthukumar, Phade, Sahai, arXiv:2012.02125v3, Eq. (3.26), p.19 (corrected: the bound
`erfc((β + C)/γ(q∗))` is replaced by positivity). In the setting of Theorem 3.4 (competitive game
`(G, H)` with Nash equilibrium `(p∗, q∗)`, both players monotonic mean-based with an optimal
no-regret rate, realization-based play), if `Q_t → q∗` almost surely then for every `β > 0`
`lim inf_{t→∞} P(√t(Q̂_t − q∗) ≥ β) > 0` and `lim inf_{t→∞} P(√t(Q̂_t − q∗) ≤ −β) > 0`.

**Formalization Note** `Q̂_t = avgAct J t` is the empirical average of player 2's realized
actions. "lim inf > 0" is stated as: some `ε > 0` bounds the probability below for all large `t`.
A positive lim inf over all `t` is equivalent to a positive lim inf along every deterministic
subsequence `t_k`, which is how the page uses it. The printed constant uses the `C` of Lemma 3.7,
which does not exist as printed, and step (ii) of the display on p.19 overstates a Gaussian tail. -/
theorem eq_3_26 {G H : Matrix (Fin 2) (Fin 2) ℝ} (hcomp : IsCompetitive G H) {p q : ℝ}
    (hNE : RankOneBimatrix.BinSearch.IsNE G H (mix p) (mix q))
    {f g : ℕ → ℝ → ℝ} (hf : IsMonotonicMeanBased f) (hg : IsMonotonicMeanBased g)
    (hfr : HasRate G (meanBased f) (1 / 2)) (hgr : HasRate Hᵀ (meanBased g) (1 / 2))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (I J : ℕ → Ω → Fin 2) (hplay : IsPlay μ (meanBased f) (meanBased g) I J)
    (hQ : ∀ᵐ ω ∂μ, Tendsto (fun n => meanBased g n (fun k : Fin n => I k ω)) atTop (𝓝 q))
    (β : ℝ) (hβ : 0 < β) :
    (∃ ε : ℝ, 0 < ε ∧ ∀ᶠ t : ℕ in atTop,
        ε ≤ (μ {ω | β ≤ Real.sqrt t * (avgAct J t ω - q)}).toReal) ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ᶠ t : ℕ in atTop,
        ε ≤ (μ {ω | Real.sqrt t * (avgAct J t ω - q) ≤ -β}).toReal) := by sorry

end NoRegretLastIterate
