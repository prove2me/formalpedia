-- Prove2me | Theorems.Thm_OAI_Saxl_wordRestrict_equivariant
-- name    : OAI.Saxl.wordRestrict_equivariant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:24:30.216776+00:00
-- url     : https://prove2.me/theorems/50b5e11d-90b2-4094-99b2-2ee5e5b063ea
-- title:
--   Restriction-contraction of word tensors to selected positions is equivariant for compatible permutations
-- statement:
--   Write $[m]=\{0,1,\dots,m-1\}$ and let $S_m$ be the symmetric group on $[m]$. For $m,d\in\mathbb{N}$ let $W_{m,d}$ be the space of functions from words $w:[m]\to[d]$ to $\mathbb{C}$, on which $S_m$ acts by $(g\cdot x)(w)=x(w\circ g)$; thus the indicator $\delta_w$ of a word is sent to $\delta_{w\circ g^{-1}}$.
--
--   Let $a,n,d,e\in\mathbb{N}$, let $i:[a]\to[n]$ be an injective map selecting $a$ of the $n$ positions, and let $j:[d]\to[e]$ be an injective map embedding a $d$-letter alphabet into an $e$-letter alphabet. The *restriction-contraction* map $R_{i,j}:W_{n,e}\to W_{a,d}$ is the linear map
--   $$
--   R_{i,j}(x)(\beta)=\sum_{\substack{\gamma:[n]\to[e]\\ \gamma\circ i=j\circ\beta}}x(\gamma)\qquad(\beta:[a]\to[d]),
--   $$
--   which prescribes the letter $j(\beta(k))$ at each selected position $i(k)$ and sums over all letters at the remaining positions.
--
--   Let $g\in S_n$ and $h\in S_a$ be compatible with $i$, in the sense that $g(i(k))=i(h(k))$ for every $k\in[a]$. Then for every $x\in W_{n,e}$,
--   $$
--   R_{i,j}(g\cdot x)=h\cdot R_{i,j}(x).
--   $$
--
--   Summing over the unselected positions amounts to contracting those tensor factors with the all-ones functional. The compatibility condition says that $g$ maps the selected positions among themselves, acting there as $h$, while it may permute the unselected positions arbitrarily. In the Pieri restriction from the Specht module of a Young diagram to that of a subdiagram, $i$ selects the positions of the cells of the subdiagram and $j$ embeds its row indices, and this lemma supplies the equivariance of that restriction map.
--
--   **Formalization Note** $R_{i,j}$ is `wordRestrict i j` with embeddings `i : Fin a ↪ Fin n` and `j : Fin d ↪ Fin e`; the action on word spaces is `wordRep`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/PieriRestriction.lean#L66-L89

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

open OAI OAI.Saxl
open scoped TensorProduct

theorem OAI.Saxl.wordRestrict_equivariant {a n d e : ℕ} (i : Fin a ↪ Fin n) (j : Fin d ↪ Fin e)
    (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin a)) (hi : ∀ k, g (i k) = i (h k))
    (x : WordSpace n e) :
    wordRestrict i j (wordRep n e g x) = wordRep a d h (wordRestrict i j x) := by sorry
