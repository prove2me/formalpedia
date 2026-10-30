-- Prove2me | Theorems.Thm_ICOTheory_Signaling_proof_prop5_threshold_iff
-- name    : ICOTheory.Signaling.proof_prop5_threshold_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:05:48.559924+00:00
-- url     : https://prove2.me/theorems/39e2d08e-5cce-4b9d-9289-92fecdce85be
-- title:
--   Proof of Proposition 5: for $t\le1$, the low type prefers revealing iff $t\le\alpha^*$
-- statement:
--   Let $\mu_L<\mu_H$, $\sigma>0$, $\gamma>0$, and let $t$ be any real number with $t\le1$. Then
--
--   $$
--   \tfrac14\mu_L\;\ge\;t\,\tfrac14\mu_H+(1-t)\,\tfrac14\mu_L-\tfrac1{32}\gamma(1-t)^2\sigma^2
--   \quad\Longleftrightarrow\quad t\le\alpha^* .
--   $$
--
--   The left side is the low type's certainty equivalent from revealing itself and selling its whole venture; the right side is its certainty equivalent from imitating the high type at the belief threshold $t$ (display (38)). The step identifies $\alpha^*$ as the largest threshold at which the low type does not imitate, which is condition (24) of the separating equilibrium.
--
--   Differences from the source:
--
--   - encoding: §4's standing conditions μ_H > μ_L (p. 18), σ the standard deviation of ξ_i² (p. 18, p. 31), γ the risk aversion of a risk-averse entrepreneur (Assumption 1(i), p. 12) → hypotheses μL < μH, 0 < σ, 0 < γ; reason: the section states them once; as binders they exclude nothing the paper admits and keep Lean's junk values of √ and / out
--   - generalization: t^i a belief threshold, which must satisfy t^i ≥ ᾱi_H (p. 20), with t^i ≤ 1 → every real t ≤ 1; reason: the step's algebra uses only t^i ≤ 1 ("Because t^i ≤ 1"); the Lean equivalence holds for every such t and specializes to the paper's thresholds t^i ∈ [ᾱi_H, 1]
-- source:
--   Chod, Lyandres, A Theory of ICOs: Diversification, Agency, and Information Asymmetry, SSRN 3159528 (December 14, 2019), proof of Proposition 5, unnumbered step, p. 31

import Mathlib
import Definitions.Def_ICOTheory_Signaling_alphaStar

namespace ICOTheory.Signaling

/-- **Proof of Proposition 5: for `t ≤ 1`, the low type prefers revealing to imitating at
threshold `t` iff `t ≤ α*`.**
Chod, Lyandres, *A Theory of ICOs: Diversification, Agency, and Information Asymmetry*,
SSRN 3159528 (December 14, 2019), proof of Proposition 5, unnumbered step, p. 31:
"`1/4 μ_L ≥ t^i 1/4 μ_H + (1 − t^i) 1/4 μ_L − 1/32 γ (1 − t^i)² σ²`. Because `t^i ≤ 1`, the above
inequality is equivalent to `t^i ≤ α*`."

For `μ_L < μ_H`, `σ > 0`, `γ > 0` and every real `t ≤ 1`,
`μ_L/4 ≥ t μ_H/4 + (1 − t) μ_L/4 − γ(1 − t)²σ²/32 ↔ t ≤ α*`.

**Formalization Note.** The two sides of the inequality are the certainty equivalents (38),
p. 31, of the low type revealing itself (`V_LL(1)`) and imitating the high type at the belief
threshold `t` (`V_LH(t)`); the constant `1/32` comes from the CARA–normal certainty
equivalent with `R_i = ξ_i²/4` and `σ` the standard deviation of `ξ_i²` (p. 31). The
statement is for every `t ≤ 1`, as printed, not only for `t ∈ [ᾱ^i_H, 1]`. -/
theorem proof_prop5_threshold_iff {μH μL σ γ : ℝ} (hμ : μL < μH) (hσ : 0 < σ) (hγ : 0 < γ)
    {t : ℝ} (ht : t ≤ 1) :
    (1 / 4) * μL ≥ t * (1 / 4) * μH + (1 - t) * (1 / 4) * μL - (1 / 32) * γ * (1 - t) ^ 2 * σ ^ 2
      ↔ t ≤ alphaStar μH μL σ γ := by sorry

end ICOTheory.Signaling
