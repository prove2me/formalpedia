-- Prove2me | Theorems.Thm_OAI_CriticalZ3_quarterFace_preimage
-- name    : OAI.CriticalZ3.quarterFace_preimage
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:50:37.438839+00:00
-- url     : https://prove2.me/theorems/2a0278bf-53d3-4459-9b42-c181a6933b04
-- title:
--   Every quarter-face is a symmetric image of the canonical one
-- statement:
--   For a centre $c\in\mathbb Z^3$ and $n\in\mathbb N$, the cube $\Lambda_n(c)$ has boundary the points with some coordinate $c_i\pm n$; it is the union of $24$ quarter-faces, each lying in one face plane $x_k=c_k\pm n$ with the other coordinates in a fixed half-range $[c_i,c_i+n]$ or $[c_i-n,c_i]$. For each quarter-face index $f$, the face symmetry (swapping the normal coordinate with coordinate $0$, applying the signs of $f$ and translating by $c$) maps the canonical quarter-face of $\Lambda_n(0)$ onto the quarter-face $f$ of $\Lambda_n(c)$:
--   $$
--   S_{c,f}^{-1}\bigl(\mathrm{QF}_f(c,n)\bigr)=\mathrm{QF}_{(0,+++)}(0,n).
--   $$
--
--   Hence all quarter-face crossing events are images of the canonical one.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/QuarterFaces.lean#L122-L163

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces

open OAI OAI.CriticalZ3
universe uE uI uV uW
open MeasureTheory ProbabilityTheory Classical
open Classical

theorem OAI.CriticalZ3.quarterFace_preimage (c : Vertex) (n : ℕ) (f : FaceIndex) :
    (faceSymmetry c f).vertex ⁻¹' QuarterFace c n f = QuarterFace 0 n canonicalFace := by sorry
