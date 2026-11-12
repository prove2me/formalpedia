-- Prove2me | Theorems.Thm_NetUnrelEst_Main_lemma_3_1
-- name    : NetUnrelEst.Main.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:15:17.349884+00:00
-- url     : https://prove2.me/theorems/d8a7f33b-217f-4d5d-b160-e8a1b3d15d02
-- title:
--   Lemma 3.1 — hypercontractive pair bound Σ_{C≠C'} a^θ_{C∪C'} ≤ z^{3/2}_{θ−2s*}, s* = log 2/λ
-- statement:
--   Let $G$ be a connected multigraph with $n\ge2$ vertices and failure probabilities $0<p_e<1$, so the capacities $w_e=-\log p_e$ are positive and finite and $\lambda$ is the minimum cut capacity. Put $s^*=\log 2/\lambda$. For every $\theta>2s^*$,
--   $$\sum_{C\ne C'}a_{C\cup C'}^{\theta}\le z_{\theta-2s^*}^{3/2},\tag{20}$$
--   where the sum is over ordered pairs of distinct cuts and $z_\vartheta=\sum_C a_C^{\vartheta}$.
--
--   At $\theta=1$ this reduces the cut-intersection theorem (Theorem 2.3) to a bound on one cut sum with slightly increased failure probabilities, which Lemma 3.2 supplies.
--
--   **Formalization Note.** Powers are real powers, and $a_{C\cup C'}$ is the product over the edges crossing $C$ or $C'$.
--
--   Differences from the source:
--   - generalization: the graph of §3.1 (the reduced graph G of §2.1 with 0 < p_e < 1) → any connected multigraph on Fin n with n ≥ 2 (self-loops and parallel edges allowed); reason: loops cross no cut and parallel edges combine into one edge with the product failure probability (§2.1), so every quantity of the statement is that of the reduced graph; the reduced graph is one instance
-- source:
--   Sun, Near-Linear Estimation of Network Unreliability, STOC 2027 submission, doi:10.5281/zenodo.23913531 (PDF sha256 eee2585a…), p. 15, Lemma 3.1

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model
import Definitions.Def_NetUnrelEst_Main_CutSums

open scoped BigOperators ENNReal

open NetUnrelDesign.Main

namespace NetUnrelEst.Main

/-- **Lemma 3.1.** For a connected multigraph with `n ≥ 2` vertices and `0 < p_e < 1`, put
`s* = log 2/λ`. For every `θ > 2s*`, `Σ_{C ≠ C'} a_{C∪C'}^θ ≤ z_{θ−2s*}^{3/2}` (20).
Sun 2027, p. 15, Lemma 3.1. -/
theorem lemma_3_1 {n m : ℕ} (ends : Ends n m) (hn : 2 ≤ n) (hconn : IsConnectedGraph ends)
    (p : Fin m → ℝ) (hp : ∀ e, 0 < p e ∧ p e < 1) (θ : ℝ)
    (hθ : 2 * (Real.log 2 / lam ends p) < θ) :
    xTheta ends p θ ≤ zTheta ends p (θ - 2 * (Real.log 2 / lam ends p)) ^ ((3 : ℝ) / 2) := by sorry

end NetUnrelEst.Main
