-- Prove2me | Theorems.Thm_OAI_Release075_BlockPresentation_rawMove_wordValue
-- name    : OAI.Release075.BlockPresentation.rawMove_wordValue
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:12:28.587982+00:00
-- url     : https://prove2.me/theorems/f5c78bb5-5f29-4012-97da-5b348526bbea
-- title:
--   Elementary homotopy moves preserve the group value of a word
-- statement:
--   For a block presentation with presented group $\Gamma$, every path in the symmetrized quiver of the triangle complex has a word of oriented edges, whose value in $\Gamma$ is the product of the generators with signs. If two paths differ by one elementary move (cancelling a backtrack $e\bar e$, or replacing $l\cdot x$ by $r$ along a triangle face), then
--   $$
--   \mathrm{val}(\mathrm{word}\,p)=\mathrm{val}(\mathrm{word}\,q).
--   $$
--
--   Hence raw-homotopic paths have the same value, and nullhomotopic loops have value $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/LiftedFilling.lean#L139-L151

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links
import Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling

open OAI OAI.Release075 OAI.Release075.BlockPresentation
open CategoryTheory
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

theorem OAI.Release075.BlockPresentation.rawMove_wordValue {a c : d.RawPaths} {p q : a ⟶ c} (h : d.RawMove p q) :
    d.wordValue (d.rawWord p) = d.wordValue (d.rawWord q) := by sorry
