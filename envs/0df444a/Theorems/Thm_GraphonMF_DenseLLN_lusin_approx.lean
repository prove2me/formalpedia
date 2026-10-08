-- Prove2me | Theorems.Thm_GraphonMF_DenseLLN_lusin_approx
-- name    : GraphonMF.DenseLLN.lusin_approx
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:30.546819+00:00
-- url     : https://prove2.me/theorems/f73de3f0-0c21-4584-a40e-8510f6e1fb0c
-- title:
--   §6.2, p. 3608 — every graphon is approximated in ‖·‖_{∞→1} by continuous graphons (Lusin)
-- statement:
--   Let $G$ be a graphon on $I=[0,1]$ and $\eta\in(0,1)$. Then there is a continuous graphon $\tilde G=\tilde G_\eta$, that is a continuous symmetric function $I\times I\to[0,1]$, such that
--   $$\|\tilde G-G\|<\eta,$$
--   where $\|\cdot\|$ is the operator norm $L^\infty(I)\to L^1(I)$ of Remark 2.1.
--
--   The proof of (3.3) uses this approximation to reduce to graphons that satisfy Condition 2.2(b).
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3608, §6.2, display after "Fix η ∈ (0,1)"

import Mathlib
import Definitions.Def_GraphonMF_DenseLLN_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GraphonMF.DenseLLN
theorem lusin_approx (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (hG : GraphonMF.Stability.IsGraphon G) (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    ∃ G' : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ, GraphonMF.Stability.IsGraphon G' ∧ Continuous (Function.uncurry G') ∧
      GraphonMF.Stability.opNorm (fun u v => G' u v - G u v) < η := by sorry
end GraphonMF.DenseLLN
