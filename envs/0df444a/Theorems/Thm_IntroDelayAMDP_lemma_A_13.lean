-- Prove2me | Theorems.Thm_IntroDelayAMDP_lemma_A_13
-- name    : IntroDelayAMDP.lemma_A_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:48:23.346197+00:00
-- url     : https://prove2.me/theorems/731f9ebf-7fa3-49df-a720-4c3b02438f5e
-- title:
--   Lemma A.13 — multiplicative comparison of occupancy measures (corrected: P satisfies the constraints of (16))
-- statement:
--   There is an absolute $c>0$ such that for every layered instance with valid $P$, every observation record with counts $N(s,a)$, every policy $\pi$ and every $\beta\ge1$: if $P$ satisfies every constraint of (16), then every $P'$ in the confidence set satisfies
--   $$\sum_{s,a}\bigl[q^{P',\pi}(s,a)-e^2q(s,a)\bigr]_+\le cSH^3\beta\sum_{s,a}\frac{q^\pi(s,a)}{\max\{1,N(s,a)\}},$$
--   where $q=\min_{P''}q^{P'',\pi}$ over the confidence set.
--
--   This is the multiplicative comparison that keeps the width of the confidence sets out of the $K$-dependent term of the regret.
--
--   Differences from the source:
--   - correction: If P ∈ P_k → if P satisfies every constraint of (16); reason: the proof uses this ("both P″ and P satisfy the constraints in Eq. (16)"), and the printed form is false because of the drop rule. Take H = 2, one action, P(s₁|s₀) = P(s₂|s₀) = ½, β = 1, and at s₀ the record of 100m times s₁ followed by 10⁴m² times s₂: the constraints at s₀ are unsatisfiable, so they are dropped and P ∈ P_k, and P′, P″ may send s₀ to s₁, s₂; the left side is ≥ 1 while the right side tends to 0 as m → ∞
--   - generalization: π_k and the data of Algorithm 1, β = log(16S²AK/δ) → any policy π, any observation record, any β ≥ 1; reason: the proof uses only β ≥ 1 and the record; the paper's case is a special case
--   - generalization: N_k(s, a) on all pairs → N = the length of the record on non-last-layer pairs and arbitrary on last-layer pairs; reason: a pair's occupancy depends only on rows of earlier layers, so last-layer rows never enter the proof's sum over non-well-observed transitions; the paper's N_k is one such choice
--   - reading: = O(·) → ≤ c·(·) with an absolute c; reason: the left side is nonnegative
--   - encoding: terminal layer S_H → no terminal layer: last-layer rows vanish and V, B are 0 beyond the last layer; reason: the paper merges S_H into one state, which affects neither q_k nor B_k (p.30)
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Lemma A.13, p.42

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_IsTransition
import Definitions.Def_IntroDelayAMDP_IsPolicy
import Definitions.Def_IntroDelayAMDP_confSet
import Definitions.Def_IntroDelayAMDP_pairConstr
import Definitions.Def_IntroDelayAMDP_qLow
import Definitions.Def_IntroDelayAMDP_occ

namespace IntroDelayAMDP

open MeasureTheory

/-- **Lemma A.13 (Multiplicative Comparison of Occupancy Measures)** (printed p.42, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)): "If `P ∈ P_k`,
then every `P′ ∈ P_k` satisfies `∑_{s,a}[q^{P′,π_k}(s, a) − e²q_k(s, a)]_+ = O(SH³β ∑_{s,a} q^{π_k}(s, a)/max{1, N_k(s, a)})`."

There is an absolute `c > 0` such that for every layered instance with valid `P`, every observation
record `obs` (which determines the empirical distributions and the confidence set `P_k = confSet L β obs`
of (16)) with counts `N(s, a) = |obs(s, a)|` for the non-last-layer pairs, every policy `π` and every
`β ≥ 1`: if `P` satisfies every constraint of (16), then for every `P′ ∈ P_k`,
`∑_{s,a} max{0, q^{P′,π}(s, a) − e² q_k(s, a)} ≤ cSH³β ∑_{s,a} q^{π}(s, a)/max{1, N(s, a)}`, where
`q_k = min_{P′′∈P_k} q^{P′′,π}`.

**Formalization Note.** Stated for any observation record, any policy (the paper's `π_k`) and any
`β ≥ 1` (the paper's `β = log(16S²AK/δ) ≥ 1`); the proof uses only `β ≥ 1`. The counts of last-layer
pairs (which observe only a terminal state) are arbitrary.

**Correction.** The hypothesis "`P ∈ P_k`" is read as "`P` satisfies the constraints of (16)", which is
what the proof uses ("both `P″` and `P` satisfy the constraints in Eq. (16)"). Literally, with the drop
rule of (16), the printed statement is false: take `H = 2`, states `s₀; s₁, s₂`, one action,
`P(s₁ | s₀) = P(s₂ | s₀) = ½`, `β = 1` and, for large `m`, a record at `s₀` of `100m` times `s₁` followed
by `10⁴m²` times `s₂`. The constraints at `s₀` are unsatisfiable, so they are dropped and `P ∈ P_k`,
and `P′, P″` may send `s₀` to `s₁`, `s₂` respectively: the left side is at least `1`, while the right
side tends to `0` as `m → ∞`. -/
theorem lemma_A_13 :
    ∃ c > (0 : ℝ), ∀ (St A : Type) [Fintype St] [DecidableEq St] [Fintype A] (H : ℕ)
      (L : LayeredSpace St H) (P : St → A → St → ℝ), IsTransition L P →
      ∀ (obs : St → A → List St) (N : St → A → ℕ),
        (∀ s a, L.layer s + 1 < H → N s a = (obs s a).length) →
      ∀ π : St → A → ℝ, IsPolicy π → ∀ β : ℝ, 1 ≤ β →
      (∀ s a, pairConstr L β (obs s a) (L.layer s) (P s a)) →
      ∀ P' ∈ confSet L β obs,
        ∑ s, ∑ a, max 0 (occ L P' π s a - Real.exp 2 * qLow L (confSet L β obs) π s a) ≤
          c * (Fintype.card St : ℝ) * (H : ℝ) ^ 3 * β *
            ∑ s, ∑ a, occ L P π s a / max 1 (N s a : ℝ) := by sorry

end IntroDelayAMDP
