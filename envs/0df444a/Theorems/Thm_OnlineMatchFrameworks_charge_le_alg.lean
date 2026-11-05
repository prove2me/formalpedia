-- Prove2me | Theorems.Thm_OnlineMatchFrameworks_charge_le_alg
-- name    : OnlineMatchFrameworks.charge_le_alg
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:33:15.972024+00:00
-- url     : https://prove2.me/theorems/0ffe744c-0baa-4f62-8524-9e4b796a78ec
-- title:
--   Proof of Lemma 2: the charges total at most $\mathrm{ALG}(G)$ (corrected: ≤ for the printed =)
-- statement:
--   Let $x$ satisfy constraint (1a) and let the black box play only available items. For every arrival order,
--   $$
--   \mathbb E\Bigl[\sum_{v}c_v(\mathrm{ALG})\Bigr]\le\mathrm{ALG}(G).
--   $$
--   So the imaginary charges never exceed the reward of the algorithm, since each matched item $u$ has at most $w_u$ assigned in total.
--
--   Differences from the source:
--   - correction: ALG(G) = E[Σ_v c_v(ALG)] (p.40) → E[Σ_v c_v(ALG)] ≤ ALG(G); reason: the equality is false: one item, one customer, p = 1/2, w = 1, patience 1 and x = 1 (optimal in LP (1)) give ALG = 1/2 and charge 1/4 + 1/8 = 3/8, proved in the sanity file; ≤ is what the sentence on p.39 gives and all the proof needs
--   - generalization: x an optimal solution of LP (1), V fully ordered → any x satisfying (1a), any list of customers, a black box that plays available items; reason: the optimal solution with a complete order is a special case
--   - generalization: patience deterministic (p.11), an arbitrary distribution (§5.2) or item hazard rates (§5.1) → one survival function S_v(l) in [0,1], sublist monotone; reason: the three models satisfy the hypotheses (proved in the sanity file), so each is a special case
--   - reading: expected size of the matching (p.14), while the setting, LP (1) and the proof use weight → expected weight, w ≥ 0; reason: size is w ≡ 1, so this is the stronger reading
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, Appendix A, proof of Lemma 2, pp.39–40, "we have assigned at most wu weight in total"

import Definitions.Def_OnlineMatchFrameworks_Charge

open scoped BigOperators

namespace OnlineMatchFrameworks

/-- **The charges total at most `ALG(G)`.** arXiv:1907.03963v6, Appendix A, proof of Lemma 2, pp.39–40,
"we have assigned at most w_u weight in total", corrected: p.40 prints `ALG(G) = E[∑_v c_v(ALG)]`,
but only `≤` holds (one item, one customer, `p = 1/2`, `w = 1`, patience `1`, `x = 1` give `ALG = 1/2`
and charge `3/8`).

**Formalization Note.** The item side (1a) is all that is used of the feasibility of `x`, and the
black box need only offer available items. -/
theorem charge_le_alg {U V : Type*} [DecidableEq U] [Fintype U] [Fintype V]
    (G : Instance U V) (BB : Finset U → V → PMF (Policy U)) (hBB : IsAvailableBlackBox BB)
    (x : U → V → ℝ) (hx : ∀ u, ∑ v, x u v * G.p u v ≤ 1) (order : List V) :
    G.chargeFrom x BB order Finset.univ ≤ G.ALG BB order := by sorry

end OnlineMatchFrameworks
