-- Prove2me | Theorems.Thm_OnlineMatchFrameworks_half_kappa_objective_le_charge
-- name    : OnlineMatchFrameworks.half_kappa_objective_le_charge
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:33:24.786289+00:00
-- url     : https://prove2.me/theorems/2a4e28c2-514d-4a7d-a75d-89ae9ba226f6
-- title:
--   Proof of Lemma 2: $\sum_v\mathbb E[c_v(\mathrm{ALG})]\ge\frac\kappa2c(x)$ (corrected: κ/2 for the printed ½)
-- statement:
--   Let $0\le\kappa\le 1$, let the black box be $\kappa$-approximate, let $x\ge 0$ satisfy (1d), and let the order be a duplicate-free list of all of $V$. Then
--   $$
--   \frac{\kappa}{2}\,c(x)\le\sum_{v}\mathbb E[c_v(\mathrm{ALG})].
--   $$
--   This is the inequality that completes Lemma 2 together with the bound of the charges by $\mathrm{ALG}(G)$.
--
--   Differences from the source:
--   - correction: Σ_v E[c_v(ALG)] ≥ ½ OPT_LP(G) (the target on p.40) → Σ_v E[c_v(ALG)] ≥ (κ/2) c(x); reason: the ½ form fails for κ < 1 (a black box that plays the empty list with probability 1 − κ); the chain below the target on the same page ends in (κ/2) OPT_LP(G)
--   - generalization: x* an optimal solution of LP (1) → any x ≥ 0 satisfying (1d); reason: the optimal solution is a special case
--   - encoding: E[Σ_v c_v(ALG)] by linearity over Pr[U_v] → the backward recursion chargeFrom; reason: total expectation over the process
--   - generalization: patience deterministic (p.11), an arbitrary distribution (§5.2) or item hazard rates (§5.1) → one survival function S_v(l) in [0,1], sublist monotone; reason: the three models satisfy the hypotheses (proved in the sanity file), so each is a special case
--   - reading: StarBB within a factor κ of optimal (pp.5, 14), κ ∈ [0,1] → a PMF over duplicate-free lists of available items with κ·OPT(A,v) ≤ expected star value, for all A, v; reason: the form the proof on p.40 uses; the weight form on p.5 implies it, and a randomized star policy is a mixture of lists
--   - reading: the order of arrival is set by an adversary (p.11) → every duplicate-free list of all of V; reason: the adversary fixes the order in advance
--   - reading: expected size of the matching (p.14), while the setting, LP (1) and the proof use weight → expected weight, w ≥ 0; reason: size is w ≡ 1, so this is the stronger reading
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, Appendix A, proof of Lemma 2, p.40, "Thus, to complete the proof"

import Definitions.Def_OnlineMatchFrameworks_Charge
import Definitions.Def_OnlineMatchFrameworks_LP

namespace OnlineMatchFrameworks

/-- **`∑_v E[c_v(ALG)] ≥ (κ/2) c(x)`.** arXiv:1907.03963v6, Appendix A, proof of Lemma 2, p.40,
corrected: the printed target is `∑_v E[c_v(ALG)] ≥ ½ OPT_LP(G)`, without `κ`, whereas the chain below it
on the same page ends in `(κ/2) OPT_LP(G)`, and the `½` form is false for `κ < 1` (a black box playing the
empty list with probability `1 - κ`). -/
theorem half_kappa_objective_le_charge {U V : Type*} [DecidableEq U] [Fintype U] [Fintype V]
    (G : Instance U V) (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (BB : Finset U → V → PMF (Policy U)) (hBB : G.IsKappaApprox κ BB)
    (x : U → V → ℝ) (hx0 : ∀ u v, 0 ≤ x u v)
    (hx : ∀ (U' : Finset U) (v : V), ∑ u ∈ U', x u v * G.p u v * G.w u ≤ G.starOpt U' v)
    (order : List V) (hnd : order.Nodup) (hall : ∀ v, v ∈ order) :
    κ / 2 * G.objective x ≤ G.chargeFrom x BB order Finset.univ := by sorry

end OnlineMatchFrameworks
