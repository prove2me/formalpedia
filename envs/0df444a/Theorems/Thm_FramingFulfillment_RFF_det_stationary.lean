-- Prove2me | Theorems.Thm_FramingFulfillment_RFF_det_stationary
-- name    : FramingFulfillment.RFF.det_stationary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:51.474406+00:00
-- url     : https://prove2.me/theorems/a8a0b4d6-46f6-41b3-8fc8-7bce84841e2b
-- title:
--   Electronic Companion EC 3, p. EC-3 — stationarity of DET': 𝒥^D(θ) = θ·𝒥^D(1)
-- statement:
--   For a JFF instance satisfying the standing assumptions and every $\theta\in\mathbb N$, let $\mathcal J^D(\theta)$ be the optimal value of DET' for the scaled instance, with horizon $\theta T$ and inventories $\theta C$. Then
--
--   $$\mathcal J^D(\theta)=\theta\cdot\mathcal J^D(1).$$
--
--   The paper derives this from the existence of a stationary optimal solution of DET'. It is how the deterministic bound grows linearly in the scale, and it is used to get the relative guarantee in Theorem 2.
--
--   **Formalization Note** The page's "DET" is DET' (the Electronic Companion treats the JFF setting throughout). The scale $\theta$ is a natural number so that the horizon $\theta T$ is an integer.
-- source:
--   Lei, Jasin, Uichanco & Vakhutinsky, Joint Product Framing and Order Fulfillment under the MNL Model, SSRN 3282019 (PDF sha256 7d6bd797…), Electronic Companion EC 3 (proof of Corollary 1), EC p. 3 = PDF p. 36

import Mathlib
import Definitions.Def_FramingFulfillment_RFF_Model

namespace FramingFulfillment.RFF

/-- Electronic Companion EC 3 (EC p. 3): by stationarity of an optimal DET' solution,
`𝒥^D(θ) = θ · 𝒥^D(1)` for every scale `θ`. -/
theorem det_stationary (P : Inst) (hP : P.Standing) (θ : ℕ) :
    (P.scale θ).JD = (θ : ℝ) * (P.scale 1).JD := by sorry

end FramingFulfillment.RFF
