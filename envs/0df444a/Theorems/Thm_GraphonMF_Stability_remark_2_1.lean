-- Prove2me | Theorems.Thm_GraphonMF_Stability_remark_2_1
-- name    : GraphonMF.Stability.remark_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:27:34.287033+00:00
-- url     : https://prove2.me/theorems/3c20f149-4f27-4771-992c-79de1b002dae
-- title:
--   Remark 2.1 — cut convergence implies operator-norm convergence
-- statement:
--   Let $G$ and every $G_n$ be graphons on $I=[0,1]$. If $G_n$ converges to $G$ in the cut norm, then the corresponding operators from $L^\infty(I)$ to $L^1(I)$ converge in operator norm:
--
--   $$\|G_n-G\|_\square\longrightarrow0\quad\Longrightarrow\quad\|G_n-G\|_{\infty\to1}\longrightarrow0.$$
--
--   This connects the graphon topology used in the target theorem to the operator bound used in the paper's stability estimate.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3590, Remark 2.1

import Mathlib
import Definitions.Def_GraphonMF_Stability_Setting

open MeasureTheory Filter Topology

namespace GraphonMF.Stability

/-- Remark 2.1, p. 3590: cut-metric convergence implies convergence in the operator norm. -/
theorem remark_2_1 (G : I → I → ℝ) (Gs : ℕ → I → I → ℝ)
    (hG : IsGraphon G) (hGs : ∀ n, IsGraphon (Gs n))
    (hcut : Tendsto (fun n => cutNorm (fun u v => Gs n u v - G u v)) atTop (𝓝 0)) :
    Tendsto (fun n => opNorm (fun u v => Gs n u v - G u v)) atTop (𝓝 0) := by sorry

end GraphonMF.Stability
