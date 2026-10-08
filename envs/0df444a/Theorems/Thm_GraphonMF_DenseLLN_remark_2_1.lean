-- Prove2me | Theorems.Thm_GraphonMF_DenseLLN_remark_2_1
-- name    : GraphonMF.DenseLLN.remark_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:23.972986+00:00
-- url     : https://prove2.me/theorems/57534cb8-dc08-4d22-aa00-994f8a70b11d
-- title:
--   Remark 2.1, p. 3590 — cut-norm convergence of graphons implies operator-norm convergence
-- statement:
--   Let $G$ and $G_n$, $n\in\mathbb N$, be graphons on $I=[0,1]$, and write $\|W\|_\square$ for the cut norm and $\|W\|=\|W\|_{\infty\to1}$ for the operator norm of a kernel viewed as an operator $L^\infty(I)\to L^1(I)$. If $\|G_n-G\|_\square\to0$, then
--   $$\|G_n-G\|=\sup_{\|g\|_\infty\le 1}\int_I\Big|\int_I (G_n-G)(u,v)\,g(v)\,dv\Big|\,du\;\longrightarrow\;0 .$$
--
--   The paper cites this from Lovász, *Large Networks and Graph Limits*, Lemma 8.11. It turns the cut-metric convergence of Condition 3.1(c) into the operator-norm convergence that Lemma 6.1 uses.
--
--   **Formalization Note** The supremum defining $\|\cdot\|_{\infty\to1}$ runs over measurable $g$ with $|g|\le1$ everywhere. The page states only the implication, so no constant (such as Lovász's factor 4) is stated.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3590, Remark 2.1

import Mathlib
import Definitions.Def_GraphonMF_DenseLLN_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GraphonMF.DenseLLN
theorem remark_2_1 (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (Gs : ℕ → GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (hG : GraphonMF.Stability.IsGraphon G)
    (hGs : ∀ n, GraphonMF.Stability.IsGraphon (Gs n))
    (hcut : Tendsto (fun n => GraphonMF.Stability.cutNorm (fun u v => Gs n u v - G u v)) atTop (𝓝 0)) :
    Tendsto (fun n => GraphonMF.Stability.opNorm (fun u v => Gs n u v - G u v)) atTop (𝓝 0) := by sorry
end GraphonMF.DenseLLN
