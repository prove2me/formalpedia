-- Prove2me | Theorems.Thm_GraphonMF_SparseLLN_remark_2_1
-- name    : GraphonMF.SparseLLN.remark_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:23.509981+00:00
-- url     : https://prove2.me/theorems/76bc4858-e7a7-4388-8b6a-dc73b93c293a
-- title:
--   Remark 2.1 — cut convergence implies operator-norm convergence
-- statement:
--   Let $G_n$ and $G$ be graphons on $I=[0,1]$. Write $\|W\|_\square$ for the supremum of the absolute integral of $W$ over measurable rectangles and $\|W\|_{\infty\to1}$ for its norm as an operator from $L^\infty(I)$ to $L^1(I)$. Then
--
--   $$\|G_n-G\|_\square\longrightarrow0\quad\Longrightarrow\quad\|G_n-G\|_{\infty\to1}\longrightarrow0.$$
--
--   This converts graph-sequence convergence into the operator estimate used by the coupling argument.
--
--   **Formalization Note** The suprema range over measurable sets and measurable test functions bounded by one. The graphon hypotheses ensure these real suprema are bounded.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3590, Remark 2.1; https://doi.org/10.1214/22-AAP1901

import Definitions.Def_GraphonMF_SparseLLN_Setting

open Filter Topology
set_option autoImplicit false

namespace GraphonMF.SparseLLN

/-- Remark 2.1, p. 3590: cut convergence implies L∞→L¹ operator-norm convergence. -/
theorem remark_2_1
    (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (Gs : ℕ → GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ)
    (hG : GraphonMF.Stability.IsGraphon G) (hGs : ∀ n, GraphonMF.Stability.IsGraphon (Gs n))
    (hcut : Tendsto (fun n => cutNorm (fun u v => Gs n u v - G u v))
      atTop (𝓝 0)) :
    Tendsto (fun n => GraphonMF.Stability.opNorm (fun u v => Gs n u v - G u v)) atTop (𝓝 0) := by sorry

end GraphonMF.SparseLLN
