-- Prove2me | Theorems.Thm_OAI_Release075_BlockPresentation_rawRectangle_nullhomotopic_of_eq_one
-- name    : OAI.Release075.BlockPresentation.rawRectangle_nullhomotopic_of_eq_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:50:20.858646+00:00
-- url     : https://prove2.me/theorems/33a6090f-ccc8-45a9-9926-49f29151dfcd
-- title:
--   A trivial rectangle word bounds a combinatorial nullhomotopy
-- statement:
--   In the presented group $\Gamma$ of a block presentation, suppose a rectangular word in the $x$-generators is trivial:
--   $$
--   x_{i,u,v}\,x_{i,u',v}^{-1}\,x_{i,u',v'}\,x_{i,u,v'}^{-1}=1 .
--   $$
--   Then the corresponding unbased four-edge loop at the vertex $v$ of the triangle complex, $x_{i,u,v}\,\overline{x_{i,u',v}}\,x_{i,u',v'}\,\overline{x_{i,u,v'}}$, is raw-homotopic to the constant path. That is, it can be reduced by finitely many backtrack cancellations and triangle moves.
--
--   This is the starting point of the planar diagram argument for rectangular nontriviality.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/WordPaths.lean#L285-L304

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths

open OAI OAI.Release075 OAI.Release075.BlockPresentation
open CategoryTheory
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

theorem OAI.Release075.BlockPresentation.rawRectangle_nullhomotopic_of_eq_one (i : I) (u u' v v' : Fin r)
    (h : d.x i u v * (d.x i u' v)⁻¹ * d.x i u' v' * (d.x i u v')⁻¹ = 1) :
    d.RawHomotopic (d.rawRectangle i u u' v v') (𝟙 _) := by sorry
