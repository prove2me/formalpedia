-- Prove2me | Theorems.Thm_NetUnrelDesign_Main_lemma_2_1
-- name    : NetUnrelDesign.Main.lemma_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:09:35.363106+00:00
-- url     : https://prove2.me/theorems/d395f4f1-2228-47c7-810f-6efd17167c66
-- title:
--   Lemma 2.1 — connectivity log-concavity: R_G(w) is log-concave in w ≥ 0 and −log R_G is convex
-- statement:
--   Let $G$ be the paper's connected multigraph on $n\ge2$ vertices, and let edges fail independently with probabilities $e^{-w_e}$, $w\in[0,\infty)^E$. Let $R_G(w)$ be the probability that the working edges form a connected graph. Then $R_G$ is log-concave on $[0,\infty)^E$: for all $w,w'\ge0$ and $\theta\in[0,1]$,
--   $$R_G(\theta w+(1-\theta)w')\ \ge\ R_G(w)^{\theta}R_G(w')^{1-\theta}.$$
--   Consequently $-\log R_G$, with the value $+\infty$ where $R_G=0$, is convex on $[0,\infty)^E$ as an extended-real function:
--   $$-\log R_G(\theta w+(1-\theta)w')\le\theta(-\log R_G(w))+(1-\theta)(-\log R_G(w')).$$
--
--   Differences from the source:
--
--   - encoding: G is the paper's network (standing assumption of §1: connected, n ≥ 2) → hypotheses 2 ≤ n and IsConnectedGraph ends; reason: the paper's graph always satisfies them; no instance of the source is excluded
--   - encoding: R_G log-concave in w ≥ 0 → R(θw+(1−θ)w') ≥ R(w)^θ R(w')^{1−θ} for w, w' ≥ 0, θ ∈ [0,1] (real powers, 0^θ = 0 for θ > 0); reason: the definition of log-concavity for a nonnegative function
--   - encoding: −log R_G with value +∞ when R_G = 0 is convex → EReal-valued negLogConnW with the convexity inequality in EReal (θ·⊤ = ⊤ for θ > 0, 0·⊤ = 0); reason: −log R_G ≥ 0, so no −∞ arises and the EReal arithmetic is the extended-value convention
-- source:
--   Sun 2026, Fast Approximation Algorithms for Minimizing Network Unreliability, doi:10.5281/zenodo.23914978 (PDF sha256 1120f100…), Lemma 2.1, p. 6 (PDF 7)

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model

open scoped BigOperators

namespace NetUnrelDesign.Main

/-- **Lemma 2.1 (Connectivity log-concavity).** For the connected multigraph `G` (`n ≥ 2`), the
probability `R_G(w)` that independent edges with failure probabilities `e^{−w_e}` form a connected
graph is log-concave in `w ≥ 0`: `R_G(θw + (1−θ)w') ≥ R_G(w)^θ R_G(w')^{1−θ}` for `w, w' ≥ 0`,
`θ ∈ [0,1]`. Thus `−log R_G`, with value `+∞` when `R_G = 0`, is convex on `[0,∞)^E` (as an
extended-real function). Sun 2026, p. 6 (PDF 7). -/
theorem lemma_2_1 {n m : ℕ} (ends : Ends n m) (hn : 2 ≤ n) (hconn : IsConnectedGraph ends) :
    (∀ w w' : Fin m → ℝ, (∀ e, 0 ≤ w e) → (∀ e, 0 ≤ w' e) → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      connW ends w ^ θ * connW ends w' ^ (1 - θ) ≤ connW ends (θ • w + (1 - θ) • w')) ∧
    (∀ w w' : Fin m → ℝ, (∀ e, 0 ≤ w e) → (∀ e, 0 ≤ w' e) → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      negLogConnW ends (θ • w + (1 - θ) • w') ≤
        (θ : EReal) * negLogConnW ends w + ((1 - θ : ℝ) : EReal) * negLogConnW ends w') := by sorry

end NetUnrelDesign.Main
