-- Prove2me | Theorems.Thm_OAI_Saxl_extendColor_count_old
-- name    : OAI.Saxl.extendColor_count_old
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:28:57.583725+00:00
-- url     : https://prove2.me/theorems/9ee0af36-52c3-4e30-90d2-15d7457cdffe
-- title:
--   Extending a coloring by a constant color preserves the sizes of the other color classes
-- statement:
--   Let $a,n\in\mathbb{N}$, write $[m]=\{0,1,\dots,m-1\}$, let $i:[a]\to[n]$ be injective and let $c:[a]\to\mathbb{N}$ be a coloring. For $p\in\mathbb{N}$, the *extension of $c$ along $i$ by the color $p$* is the coloring $c^{i,p}:[n]\to\mathbb{N}$,
--   $$
--   c^{i,p}(x)=\begin{cases}c(k), & \text{if } x=i(k) \text{ for some } k\in[a],\\ p, & \text{if } x\notin i([a]).\end{cases}
--   $$
--
--   Let $q,j\in\mathbb{N}$ with $j\neq q$. Then the color class of $j$ has the same size before and after extending by $q$:
--   $$
--   \#\{x\in[n]:\ c^{i,q}(x)=j\}=\#\{k\in[a]:\ c(k)=j\}.
--   $$
--
--   When a coloring of the positions of a smaller tableau is transported to a larger tableau and all new positions receive a fresh color, the old color classes keep their sizes. This is the bookkeeping step in the inductive construction of strip colorings for iterated Pieri restrictions.
--
--   **Formalization Note** $c^{i,q}$ is `extendColor i c q` with `i : Fin a ↪ Fin n` and `c : Fin a → ℕ`; the cardinalities are those of `Finset.univ.filter`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/StripExtension.lean#L82-L101

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Definitions.Def_OAI_RepresentationTheory_Saxl_SupportSeparation
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandOrbit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandGlue
import Definitions.Def_OAI_RepresentationTheory_Saxl_SignEquivalence
import Definitions.Def_OAI_RepresentationTheory_Saxl_PieriRestriction
import Definitions.Def_OAI_RepresentationTheory_Saxl_StripExtension

open OAI OAI.Saxl
open scoped TensorProduct

theorem OAI.Saxl.extendColor_count_old {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q j : ℕ)
    (hj : j ≠ q) :
    (Finset.univ.filter (fun x => extendColor i c q x = j)).card =
      (Finset.univ.filter (fun x => c x = j)).card := by sorry
