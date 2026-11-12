-- Prove2me | Theorems.Thm_NetUnrelEst_Main_lemma_D_1
-- name    : NetUnrelEst.Main.lemma_D_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:15:35.236976+00:00
-- url     : https://prove2.me/theorems/50291046-f3dc-488f-8777-b0564ed99938
-- title:
--   Lemma D.1 — the number of components K_t concentrates on scale √n
-- statement:
--   There is an absolute constant $c_r>0$ such that, for every connected multigraph with $n\ge2$ vertices and failure probabilities $0<p_e<1$, every deterministic time $0\le t\le1$ and every $0\le x\le n$,
--   $$\Pr\big(|K_t-\mathbb EK_t|\ge x\big)\le 2\exp(-c_rx^2/n),$$
--   where $K_t$ is the number of components of $(V,\{e:T_e\le t\})$ for independent exponential arrival times $T_e$ of rate $-\log p_e$.
--
--   The algorithm reads its early contraction times off one random contraction trajectory. Concentration of $K_t$ at scale $\sqrt n$ is what makes the observed hitting times reliable estimates of the deterministic quantiles of $F$.
--
--   **Formalization Note.** At a fixed time $t$, edge $e$ has arrived with probability $1-p_e^t$, so the law of $K_t$ is that of the number of working components when $e$ fails with probability $p_e^t$. The probability is a finite sum, and $c_r$ is quantified before the graph, $t$ and $x$.
--
--   Differences from the source:
--   - generalization: the ordinary contraction of the reduced graph G of §2.1 (0 < p_e < 1) → any connected multigraph on Fin n with n ≥ 2 (self-loops and parallel edges allowed); reason: loops cross no cut and parallel edges combine into one edge with the product failure probability (§2.1), so every quantity of the statement is that of the reduced graph; the reduced graph is one instance
--   - encoding: K_t for independent exponential arrival times at a deterministic time t of the contraction experiment → components of the working graph when edge e fails with probability p_e^t, for 0 ≤ t ≤ 1; reason: the law of the arrived set at a fixed time; the experiment runs on [0, 1]
-- source:
--   Sun, Near-Linear Estimation of Network Unreliability, STOC 2027 submission, doi:10.5281/zenodo.23913531 (PDF sha256 eee2585a…), p. 36, Lemma D.1

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model
import Definitions.Def_NetUnrelEst_Main_Contraction

open scoped BigOperators ENNReal

open NetUnrelDesign.Main

namespace NetUnrelEst.Main

/-- **Lemma D.1.** There is an absolute constant `c_r > 0` such that for every connected multigraph
with `n ≥ 2` vertices and `0 < p_e < 1`, every deterministic time `0 ≤ t ≤ 1` and every
`0 ≤ x ≤ n`, `Pr(|K_t − EK_t| ≥ x) ≤ 2 exp(−c_r x²/n)`. Sun 2027, p. 36, Lemma D.1. -/
theorem lemma_D_1 :
    ∃ cr : ℝ, 0 < cr ∧ ∀ {n m : ℕ} (ends : Ends n m), 2 ≤ n → IsConnectedGraph ends →
      ∀ p : Fin m → ℝ, (∀ e, 0 < p e ∧ p e < 1) → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        ∀ x : ℝ, 0 ≤ x → x ≤ n →
          prob (atTime p t) (fun F => x ≤ |(numComponents ends F : ℝ) - meanK ends p t|) ≤
            2 * Real.exp (-(cr * x ^ 2) / n) := by sorry

end NetUnrelEst.Main
