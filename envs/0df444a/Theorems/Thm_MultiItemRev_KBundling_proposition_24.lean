-- Prove2me | Theorems.Thm_MultiItemRev_KBundling_proposition_24
-- name    : MultiItemRev.KBundling.proposition_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:11:45.154528+00:00
-- url     : https://prove2.me/theorems/9c73a745-5c07-4180-b4a8-865c7eaf80bb
-- title:
--   Proposition 24, p. 39 — for i.i.d.-ER V₁, V₂: BRev(V₁, V₂) = Rev(V₁ + V₂) = 2(w + 1)
-- statement:
--   Let $w\approx0.278$ be the solution of $w\,e^{w+1}=1$.
--
--   **Proposition 24.** Let $V_1,V_2$ be i.i.d.-ER. Then
--   $$\mathrm{BRev}(V_1,V_2)=\mathrm{Rev}(V_1+V_2)=2(w+1).$$
--
--   This is Proposition 12 (iii) of the paper. It shows that bundling two ER goods earns $2(w+1)\approx2.56$, against $\mathrm{SRev}=2$ from selling them separately, and it is the source of the constant $1/(w+1)$ in Proposition 13 (i).
--
--   **Formalization Note** $w$ is a real parameter with the hypothesis $w\,e^{w+1}=1$, which determines it uniquely; no Lambert-$W$ function is used. The second conjunct states $\mathrm{Rev}(V_1+V_2)$ with the sum written as $x_0+x_1$.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 39, Proposition 24 (= Proposition 12 (iii), p. 22); w defined on p. 22

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model
import Definitions.Def_MultiItemRev_KSeparate_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.KBundling

theorem proposition_24 (w : ℝ) (hw : w * Real.exp (w + 1) = 1) :
    MultiItemRev.Decomp.BRev (Measure.pi (fun _ : Fin 2 => MultiItemRev.KSeparate.erLaw)) = ENNReal.ofReal (2 * (w + 1)) ∧
    MultiItemRev.Decomp.Rev1 ((Measure.pi (fun _ : Fin 2 => MultiItemRev.KSeparate.erLaw)).map (fun x => x 0 + x 1)) =
      ENNReal.ofReal (2 * (w + 1)) := by sorry

end MultiItemRev.KBundling
