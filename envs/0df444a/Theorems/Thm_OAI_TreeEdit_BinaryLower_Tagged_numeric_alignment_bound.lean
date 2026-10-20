-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_Tagged_numeric_alignment_bound
-- name    : OAI.TreeEdit.BinaryLower.Tagged.numeric_alignment_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:19:10.792112+00:00
-- url     : https://prove2.me/theorems/82540ebf-697b-42a4-908c-fa9730b3e501
-- title:
--   Numerical loss bound for tag-respecting alignments
-- statement:
--   Words of length $TmB$ are read as $T$ rows of $m$ blocks of width $B$: position $t$ lies in block $\lfloor t/B\rfloor$, with tag $\lfloor t/B\rfloor\bmod m$ and row $\lfloor\lfloor t/B\rfloor/m\rfloor$. Let $m\ge2$, $B>0$, and let $u,v$ be strictly increasing sequences of $L$ positions below $TmB$ with $\mathrm{tag}(u_i)=\mathrm{tag}(v_i)$. Let $0\le d\le mB$, and suppose each pair of rows receives at most $mB-d$ matches. Then, with $g=(m-1)B$,
--   $$
--   \frac{T\,d\,g}{d+g}\le TmB-L .
--   $$
--
--   Each row either splits, losing $g$, or stays, losing $d$; the worst mix gives this bound.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/TaggedAlignment.lean#L15-L54

import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Tagged
open Finset

theorem OAI.TreeEdit.BinaryLower.Tagged.numeric_alignment_bound {L T m B : ℕ} (hm : 2 ≤ m) (hB : 0 < B)
    (u v : Fin L → ℕ) (hu : StrictMono u) (hv : StrictMono v)
    (hub : ∀ i, u i < T * m * B) (hvb : ∀ i, v i < T * m * B)
    (htags : ∀ i, u i / B % m = v i / B % m)
    (d : ℝ) (hd : 0 ≤ d) (hdW : d ≤ (m * B : ℕ))
    (hlocal : ∀ a < T, ∀ b < T,
      ((univ.filter fun i : Fin L =>
        u i / B / m = a ∧ v i / B / m = b).card : ℝ) ≤ (m * B : ℕ) - d) :
    (T : ℝ) * d * (((m - 1) * B : ℕ) : ℝ) /
        (d + (((m - 1) * B : ℕ) : ℝ)) ≤
      (T * m * B : ℕ) - (L : ℝ) := by sorry
