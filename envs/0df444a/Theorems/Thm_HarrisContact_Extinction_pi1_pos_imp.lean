-- Prove2me | Theorems.Thm_HarrisContact_Extinction_pi1_pos_imp
-- name    : HarrisContact.Extinction.pi1_pos_imp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:55:13.662318+00:00
-- url     : https://prove2.me/theorems/36ca7fb0-a788-4978-b640-3ff88eaa4add
-- title:
--   §7, proof of Theorem 7.1, p. 981 — for μ = 1, λ_k = kλ: (2d − 1)λ ≥ 1 if π₁ > 0
-- statement:
--   Consider the contact process on $Z_d$ ($d\ge1$) with $\mu=1$ and $\lambda_k=k\lambda$, $\lambda\ge0$, and let $\pi_1=p_\infty(\{x\})$ be the probability that the process started from a single site $x$ survives forever. If $\pi_1>0$, then
--   $$(2d-1)\lambda\ge1 .$$
--
--   Equivalently, if $(2d-1)\lambda<1$ the process started from one site dies out almost surely. This is the conclusion of the proof of Theorem 7.1 in the normalized linear case, before the reduction by comparison and time scaling.
--
--   **Formalization Note** $2d-1$ is computed in the reals as $2d-1$ with $d\ge1$, which agrees with the natural-number difference.
-- source:
--   Harris (Ann. Probab. 2, 1974), §7, proof of Theorem 7.1, p. 981 ("(2d − 1)λ ≧ 1 if π₁ > 0")

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.Extinction

/-- §7, last sentence of the proof of Theorem 7.1 (p. 981): with μ = 1 and λ_k = kλ,
(2d − 1)λ ≥ 1 if π₁ > 0. -/
theorem pi1_pos_imp {d : ℕ} (hd : 1 ≤ d) (l : ℝ) (hl : 0 ≤ l) :
    ∀ x : Site d, 0 < survInf 1 (fun k => (k : ℝ) * l) {x} → 1 ≤ (2 * (d : ℝ) - 1) * l := by sorry

end HarrisContact.Extinction
