-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteActivity_finite_tree_l1_mean_bound
-- name    : OAI.TreeEdit.BinaryLower.FiniteActivity.finite_tree_l1_mean_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:46:00.6082+00:00
-- url     : https://prove2.me/theorems/d502fd88-d7ac-4bc7-aa65-fb78745dbf4f
-- title:
--   Average root displacement of an l1 map on the tree group
-- statement:
--   Let $A$ be a finite abelian group, $w$ assign an element of $A$ to every node of the complete $m$-ary tree of depth $h$, and call a node active for a character $\chi$ if $\chi(w(v))\ne1$. A node is sparse if it is active with fewer than $b$ active children. Leaves $f$ come with cyclic coordinates $\varphi_f:\mathbb Z/Q_f\to A$ satisfying $w(f)=\varphi_f(1)$, and $\mathbb E$ denotes the uniform average. Let $F:A\to\ell_1$ satisfy, for all $x$, the leaf bounds $\|F(x+\varphi_fz)-F(x)\|\le M/m^h$ and the node bounds $\|F(x+\mathrm{shift}(v,s))-F(x)\|\le C/m^{j}$ for nodes $v$ of depth $j$, where the shifts detect sparse nodes. Then
--   $$
--   \mathbb E_x\|F(x+w(\varnothing))-F(x)\|_1\le4\Bigl(hC+\frac M{2b^h}\Bigr).
--   $$
--
--   A map that moves leaves and node shifts little also moves the root translation little on average.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteL1Tree.lean#L21-L50

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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteActivity
open Classical
open scoped BigOperators

theorem OAI.TreeEdit.BinaryLower.FiniteActivity.finite_tree_l1_mean_bound {A σ : Type*}
    [AddCommGroup A] [Fintype A] [Fintype σ] [Nonempty σ]
    (m b h : ℕ) (hm : m ≠ 0) (hb : 0 < b)
    (w : List (Fin m) → A)
    (Q : (Fin h → Fin m) → ℕ) [∀ f, NeZero (Q f)]
    (φ : ∀ f, ZMod (Q f) →+ A)
    (hgen : ∀ f : Fin h → Fin m, w (List.ofFn f) = φ f 1)
    (F : A → RealL1)
    (shift : InternalNode (Fin m) h → σ → A) (M C : ℝ)
    (hleaf : ∀ f (z : ZMod (Q f)) x,
      ‖F (x + φ f z) - F x‖ ≤ M / (m : ℝ) ^ h)
    (hdetect : ∀ v χ, characterSparse w b v χ →
      (Fintype.card σ : ℝ) ≤ ∑ s, ‖1 - χ (shift v s)‖ ^ 2)
    (hcost : ∀ v s x,
      ‖F (x + shift v s) - F x‖ ≤ C / (m : ℝ) ^ (v.1 : ℕ)) :
    (𝔼 x : A, ‖F (x + w []) - F x‖) ≤
      4 * ((h : ℝ) * C + M / (2 * (b : ℝ) ^ h)) := by sorry
