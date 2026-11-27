-- Prove2me | Theorems.Thm_FreeOrderEPTAS_Supplement_claim_6_3
-- name    : FreeOrderEPTAS.Supplement.claim_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:41:33.89355+00:00
-- url     : https://prove2.me/theorems/b7c3d2a3-c115-4307-9b0a-f327a445fa53
-- title:
--   Claim 6.3 — a permutation for $Y$ converts to a solution with utility at least $V_Y(\sigma)$
-- statement:
--   Let $(X,c)$ be an instance of Pandora's Box with Commitment, $\kappa_i$ Weitzman's indices and $Y_i=\min\{X_i,\kappa_i\}$. For every permutation $\sigma$, the converted solution of Claim 6.3 (probe in the order $\sigma$ the boxes whose optimal threshold $t_s$ for $Y$ is at most $\kappa_{\sigma(s)}$, and select the first $X_{\sigma(s)}\ge t_s$) has expected utility
--   $$\mathbb E\Big[X_{\sigma'(\tau')}-\sum_{t\le\tau'}c_{\sigma'(t)}\Big]\ \ge\ V_Y(\sigma),$$
--   where $V_Y(\sigma)$ is the value of the optimal stopping rule for $Y$ on $\sigma$.
--
--   This is the second half of the reduction of Theorem 6.1, and holds for every permutation, not only an optimal one.
--
--   Differences from the source:
--   - encoding: Y_i = min{X_i, κ_i} → Y_i = max{min{X_i, κ_i}, 0}, and Y_i = X_i for κ_i = ∞; reason: the base instance requires non-negative values; the clip changes Y_i only when κ_i < 0 (c_i > E[X_i]), where Y_i is a.s. the constant κ_i < 0 resp. 0, and neither ever raises a stopping value
--   - reading: a solution is a probing permutation σ and a stopping rule τ (p.30), and the proofs of Claims 6.2–6.3 skip boxes the policy does not probe → a solution is either the empty solution (probe no box, utility 0) or a pair (σ, τ); a rule that never stops selects nothing and pays all n costs; reason: skipping every box must be a solution: if the only solutions were pairs (σ, τ), each probes at least one box, and for n = 1, X_1 = 0, c_1 = 1 every solution has utility −1 while V_Y(σ) = 0, so Claim 6.3 would be false and Theorem 6.1 false for α < 1
--   - generalization: all random variables are continuous (footnote 1, p.31, an assumption of the proof) → every non-negative integrable law; reason: κ_i exists and is unique for every integrable law with c_i > 0, and the per-box identities of both claims need no continuity; the continuous case is a special case
--   - reading: "the permutation σ can be converted" (the conversion of the proof, p.32) → the explicit conversion convert P σ: thresholds t_s = R_{s+1} of Y on σ; the boxes with t_s ≤ κ_{σ(s)} are probed first in the order σ and the first X ≥ t is selected, stopping at the last of them in any case; the empty solution if there is none; reason: this is the proof's conversion; skipped boxes are moved to the end and never reached, and stopping at the last kept box selects X ≥ 0 instead of nothing
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, Claim 6.3, p.32

import Mathlib
import Definitions.Def_FreeOrderEPTAS_Supplement_convert
import Definitions.Def_FreeOrderEPTAS_V

namespace FreeOrderEPTAS.Supplement

/-- Claim 6.3 (arXiv:2007.13121v3, p.32): every permutation `σ` converts to a solution of Pandora's
Box with Commitment with expected utility at least `V_Y(σ)`, the value of the optimal stopping rule
for `Y` on `σ`. The conversion is `convert`: probe in the order `σ` the boxes whose threshold
`t_s = R_{s+1}` is at most `κ_{σ(s)}`, and select the first `X ≥ t`. -/
theorem claim_6_3 {n : ℕ} (P : PandoraInstance n) (σ : Equiv.Perm (Fin n)) :
    V (Ylaw P) σ ≤ pandoraValue P (convert P σ) := by sorry

end FreeOrderEPTAS.Supplement
