-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteActivity_finite_tree_spectral_bound
-- name    : OAI.TreeEdit.BinaryLower.FiniteActivity.finite_tree_spectral_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:39:40.7153+00:00
-- url     : https://prove2.me/theorems/1bed0ad5-3c4d-47b1-a512-fd2a37a98ca6
-- title:
--   Spectral bound for the root translation of a tree
-- statement:
--   Let $A$ be a finite abelian group, $w$ assign an element of $A$ to every node of the complete $m$-ary tree of depth $h$, and call a node active for a character $\chi$ if $\chi(w(v))\ne1$. A node is sparse if it is active with fewer than $b$ active children. Leaves $f$ come with cyclic coordinates $\varphi_f:\mathbb Z/Q_f\to A$ satisfying $w(f)=\varphi_f(1)$, and $\mathbb E$ denotes the uniform average. Let $H\ge0$ on characters. Suppose each leaf translation satisfies $\sum_\chi|1-\chi(\varphi_f z)|^2H(\chi)\le M/m^h$. Sparse nodes $v$ are detected by shifts, $|\sigma|\le\sum_s|1-\chi(\mathrm{shift}(v,s))|^2$, each shift at a node of depth $j$ costing at most $C/m^j$. Then
--   $$
--   \sum_\chi|1-\chi(w(\varnothing))|^2H(\chi)\le4\Bigl(hC+\frac M{2b^h}\Bigr).
--   $$
--
--   The first term pays for sparse nodes level by level; the second shrinks with the branching.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteSpectralTree.lean#L21-L54

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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteActivity
open Classical
open scoped BigOperators

theorem OAI.TreeEdit.BinaryLower.FiniteActivity.finite_tree_spectral_bound {A σ : Type*}
    [AddCommGroup A] [Fintype A] [Fintype σ] [Nonempty σ]
    (m b h : ℕ) (hm : m ≠ 0) (hb : 0 < b)
    (w : List (Fin m) → A)
    (Q : (Fin h → Fin m) → ℕ) [∀ f, NeZero (Q f)]
    (φ : ∀ f, ZMod (Q f) →+ A)
    (hgen : ∀ f : Fin h → Fin m, w (List.ofFn f) = φ f 1)
    (H : AddChar A ℂ → ℝ) (hH : ∀ χ, 0 ≤ H χ)
    (shift : InternalNode (Fin m) h → σ → A) (M C : ℝ)
    (hleaf : ∀ f (z : ZMod (Q f)),
      (∑ χ, ‖1 - χ (φ f z)‖ ^ 2 * H χ) ≤ M / (m : ℝ) ^ h)
    (hdetect : ∀ v χ, characterSparse w b v χ →
      (Fintype.card σ : ℝ) ≤ ∑ s, ‖1 - χ (shift v s)‖ ^ 2)
    (hcost : ∀ v s,
      (∑ χ, ‖1 - χ (shift v s)‖ ^ 2 * H χ) ≤ C / (m : ℝ) ^ (v.1 : ℕ)) :
    (∑ χ : AddChar A ℂ, ‖1 - χ (w [])‖ ^ 2 * H χ) ≤
      4 * ((h : ℝ) * C + M / (2 * (b : ℝ) ^ h)) := by sorry
