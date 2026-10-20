-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_TreeDistortion_FiniteMass_root_bound_of_cyclic_leaf_tests
-- name    : OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.root_bound_of_cyclic_leaf_tests
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:31:20.349989+00:00
-- url     : https://prove2.me/theorems/1ff3c4a1-60ef-4512-836f-6628eed99acf
-- title:
--   Spectral root bound with cyclic leaf tests
-- statement:
--   Let $A$ be a finite abelian group, $\widehat A$ its characters, and $H:\widehat A\to[0,\infty)$ a spectral mass. For an element $z$, $|1-\chi(z)|^2$ measures how much $\chi$ sees the translation by $z$; for a $\{0,1\}$-valued $f$ with $H=|\hat f|^2$, $\sum_\chi|1-\chi(z)|^2H(\chi)$ is the average of $|f(x+z)-f(x)|$. Let $\varphi_u:\mathbb Z/Q_u\to A$ be homomorphisms indexed by leaves $u$, and call $u$ active for $\chi$ if $\chi(\varphi_u(1))\ne1$. Assume the hypotheses of the sparse/dense root bound, with the leaf budget replaced by: for every $u$ and $z\in\mathbb Z/Q_u$,
--   $$
--   \sum_\chi|1-\chi(\varphi_u z)|^2H(\chi)\le C_u ,
--   $$
--   and $\sum_uC_u\le M$. Then $\sum_\chi|1-\chi(\mathrm{root})|^2H(\chi)\le4(\varepsilon+M/(2K))$.
--
--   Leaf masses are controlled by translations within each leaf's cyclic coordinate.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/SparseActivity.lean#L390-L428

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open scoped BigOperators
open Classical

theorem OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.root_bound_of_cyclic_leaf_tests {A κ ν σ : Type*}
    [AddCommGroup A] [Fintype A] [Fintype κ] [Fintype ν] [Fintype σ]
    (Q : κ → ℕ) [∀ u, NeZero (Q u)] (φ : ∀ u, ZMod (Q u) →+ A)
    (H : AddChar A ℂ → ℝ) (root : A) (bad : ν → AddChar A ℂ → Prop)
    (a : ν → σ → AddChar A ℂ → ℝ) (B : ν → ℝ) (C : κ → ℝ)
    (M ε K : ℝ) (hK : 0 < K) (hH : ∀ χ, 0 ≤ H χ)
    (hdense : ∀ χ, χ root ≠ 1 → (¬ ∃ v, bad v χ) →
      K ≤ ((Finset.univ.filter (fun u => χ (φ u 1) ≠ 1)).card : ℝ))
    (hleaf : ∀ u (z : ZMod (Q u)),
      (∑ χ, ‖1 - χ (φ u z)‖ ^ 2 * H χ) ≤ C u)
    (hleafBudget : (∑ u, C u) ≤ M)
    (ha : ∀ v s χ, 0 ≤ a v s χ)
    (hdetect : ∀ v χ, bad v χ → 1 ≤ ∑ s, a v s χ)
    (hcost : ∀ v, (∑ s, ∑ χ, a v s χ * H χ) ≤ B v)
    (hbudget : (∑ v, B v) ≤ ε) :
    (∑ χ : AddChar A ℂ, ‖1 - χ root‖ ^ 2 * H χ) ≤
      4 * (ε + M / (2 * K)) := by sorry
