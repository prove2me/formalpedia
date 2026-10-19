-- Prove2me | Theorems.Thm_OAI_Saxl_extendColor_count_new
-- name    : OAI.Saxl.extendColor_count_new
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:31:55.19982+00:00
-- url     : https://prove2.me/theorems/23d9c0d4-63ab-4932-b12e-37b5af06ba35
-- title:
--   The fresh color of an extended coloring occupies exactly $n-a$ positions
-- statement:
--   Let $a,n\in\mathbb{N}$, write $[m]=\{0,1,\dots,m-1\}$, let $i:[a]\to[n]$ be injective and let $c:[a]\to\mathbb{N}$ be a coloring. For $p\in\mathbb{N}$, the *extension of $c$ along $i$ by the color $p$* is the coloring $c^{i,p}:[n]\to\mathbb{N}$,
--   $$
--   c^{i,p}(x)=\begin{cases}c(k), & \text{if } x=i(k) \text{ for some } k\in[a],\\ p, & \text{if } x\notin i([a]).\end{cases}
--   $$
--
--   Let $q\in\mathbb{N}$ and assume $c(k)\le q$ for every $k\in[a]$. Then the fresh color $q+1$ of the extension $c^{i,q+1}$ is used exactly $n-a$ times:
--   $$
--   \#\{x\in[n]:\ c^{i,q+1}(x)=q+1\}=n-a .
--   $$
--
--   The hypothesis $c\le q$ ensures that no old position already carries the color $q+1$. In the inductive construction of strip colorings, this computes the size of the color class of a newly added horizontal strip as the difference of the sizes of the two diagrams.
--
--   **Formalization Note** $c^{i,q+1}$ is `extendColor i c (q+1)`. The right-hand side `n-a` is truncated natural subtraction, but $a\le n$ holds automatically because $i$ is injective, so no truncation occurs.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/StripExtension.lean#L103-L116

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

theorem OAI.Saxl.extendColor_count_new {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q : ℕ)
    (hc : ∀ x, c x ≤ q) :
    (Finset.univ.filter (fun x => extendColor i c (q+1) x = q+1)).card = n-a := by sorry
