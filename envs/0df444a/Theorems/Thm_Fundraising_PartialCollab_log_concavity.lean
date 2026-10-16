-- Prove2me | Theorems.Thm_Fundraising_PartialCollab_log_concavity
-- name    : Fundraising.PartialCollab.log_concavity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:03:12.303007+00:00
-- url     : https://prove2.me/theorems/d3326a89-e0b0-45e8-a403-5508e9ab6cd6
-- title:
--   Proof of Proposition 4, p. S13 — δ_i(s_i)θ^p_i(s) is log-concave in s_i
-- statement:
--   Consider the partial-collaboration game under its standing hypotheses; in particular the unit performance $\delta_i$ is positive and concave on an open interval containing $[a_i, b_i]$. Fix an HO $i$ and the base utilities $s_{-i}$ of the other HOs. Then the performance per contacted donor
--   $$\sigma \longmapsto \delta_i(\sigma)\, \theta^p_i(\sigma, s_{-i}), \qquad \theta^p_i(\sigma, s_{-i}) = \frac{e^{\sigma}}{1 + e^{\sigma} + \sum_{j \ne i} e^{s_j}},$$
--   is log-concave on $[a_i, b_i]$: $\sigma \mapsto \log\left(\delta_i(\sigma)\theta^p_i(\sigma, s_{-i})\right)$ is concave there.
--
--   Log-concavity is what makes the first-order (KKT) conditions (11) necessary and sufficient for HO $i$'s choice of base utility.
--
--   **Formalization Note** Stated as `ConcaveOn` of `Real.log` of the product on $[a_i, b_i]$, as the paper's sentence claims; the product is positive there, so the logarithm is the genuine one.
-- source:
--   Aflaki, Pedraza-Martinez, Competition and Collaboration on Fundraising for Short-Term Disaster Response: The Impact on Earmarking and Performance, SSRN 3705595 (version of December 2022), p. S13 (PDF 46), proof of Proposition 4, sentence after (S11)

import Mathlib
import Definitions.Def_Fundraising_PartialCollab_Setting

namespace Fundraising.PartialCollab

/-- Proof of Proposition 4, p. S13: `δ_i(s_i) θ^p_i(s)` is log-concave in `s_i` on `[a_i, b_i]`,
the other base utilities being fixed. -/
theorem log_concavity {n : ℕ} (G : Setting n) (hG : G.Standing) (i : Fin n)
    (s : Fin n → ℝ) :
    ConcaveOn ℝ (Set.Icc (G.a i) (G.b i))
      (fun t => Real.log (G.δ i t * theta (Function.update s i t) i)) := by sorry

end Fundraising.PartialCollab
