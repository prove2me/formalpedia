-- Prove2me | Theorems.Thm_FreeOrderEPTAS_Supplement_claim_6_2
-- name    : FreeOrderEPTAS.Supplement.claim_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:40:38.710546+00:00
-- url     : https://prove2.me/theorems/8c990a07-a808-554e-854a-611a333444a3
-- title:
--   Claim 6.2 — $V_Y(\sigma^*)\ge\mathrm{OPT}(X,c)$
-- statement:
--   Let $(X,c)$ be an instance of Pandora's Box with Commitment, $\kappa_i$ Weitzman's indices and $Y_i=\min\{X_i,\kappa_i\}$. Then the optimum of Free-Order Prophets on $Y$ is at least the optimum of Pandora's Box with Commitment on $(X,c)$:
--   $$V_Y(\sigma^*)\ \ge\ \mathrm{OPT}(X,c).$$
--
--   This is the first half of the reduction of Theorem 6.1: an approximately optimal order for $Y$ is compared with $\mathrm{OPT}(X,c)$ through it.
--
--   **Formalization Note** $V_Y(\sigma^*)$ is the base `OPT` of the instance `Ylaw P`, the maximum of $V_Y$ over all permutations.
--
--   Differences from the source:
--   - encoding: Y_i = min{X_i, κ_i} → Y_i = max{min{X_i, κ_i}, 0}, and Y_i = X_i for κ_i = ∞; reason: the base instance requires non-negative values; the clip changes Y_i only when κ_i < 0 (c_i > E[X_i]), where Y_i is a.s. the constant κ_i < 0 resp. 0, and neither ever raises a stopping value
--   - reading: a solution is a probing permutation σ and a stopping rule τ (p.30), and the proofs of Claims 6.2–6.3 skip boxes the policy does not probe → a solution is either the empty solution (probe no box, utility 0) or a pair (σ, τ); a rule that never stops selects nothing and pays all n costs; reason: skipping every box must be a solution: if the only solutions were pairs (σ, τ), each probes at least one box, and for n = 1, X_1 = 0, c_1 = 1 every solution has utility −1 while V_Y(σ) = 0, so Claim 6.3 would be false and Theorem 6.1 false for α < 1
--   - generalization: all random variables are continuous (footnote 1, p.31, an assumption of the proof) → every non-negative integrable law; reason: κ_i exists and is unique for every integrable law with c_i > 0, and the per-box identities of both claims need no continuity; the continuous case is a special case
--   - encoding: V_Y(σ*) for an optimal permutation σ* of Y → OPT (Ylaw P), the maximum of V over all permutations; reason: the base definition OPT = V(σ*) = max_σ V(σ) (p.17)
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, Claim 6.2, p.31

import Mathlib
import Definitions.Def_FreeOrderEPTAS_Supplement_pandoraOPT
import Definitions.Def_FreeOrderEPTAS_Supplement_Ylaw
import Definitions.Def_FreeOrderEPTAS_OPT

namespace FreeOrderEPTAS.Supplement

/-- Claim 6.2 (arXiv:2007.13121v3, p.31): `V_Y(σ*) ≥ OPT(X, c)`. The optimum of Free-Order Prophets
on `Y_i = min{X_i, κ_i}` is at least the optimum of Pandora's Box with Commitment on `(X, c)`. -/
theorem claim_6_2 {n : ℕ} (P : PandoraInstance n) : pandoraOPT P ≤ OPT (Ylaw P) := by sorry

end FreeOrderEPTAS.Supplement
