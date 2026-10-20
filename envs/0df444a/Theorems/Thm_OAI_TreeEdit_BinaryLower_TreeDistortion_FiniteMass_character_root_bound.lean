-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_TreeDistortion_FiniteMass_character_root_bound
-- name    : OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.character_root_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:27:51.085594+00:00
-- url     : https://prove2.me/theorems/0520dd75-5302-4bde-8e5e-2739991e4cda
-- title:
--   Spectral root bound from sparse and dense characters
-- statement:
--   Let $A$ be a finite abelian group, $\widehat A$ its characters, and $H:\widehat A\to[0,\infty)$ a spectral mass. For an element $z$, $|1-\chi(z)|^2$ measures how much $\chi$ sees the translation by $z$; for a $\{0,1\}$-valued $f$ with $H=|\hat f|^2$, $\sum_\chi|1-\chi(z)|^2H(\chi)$ is the average of $|f(x+z)-f(x)|$. Fix $\mathrm{root}\in A$, leaves $u$ with activity predicates, bad-node predicates, test weights $a_{v,s}(\chi)\ge0$ and constants $K>0$, $M$, $\varepsilon$. Assume: each $\chi$ with $\chi(\mathrm{root})\ne1$ and no bad node has at least $K$ active leaves; each leaf has twice its active mass at most $C_u$, with $\sum_uC_u\le M$; and bad characters are detected, $\sum_sa_{v,s}(\chi)\ge1$, with total test cost at most $\varepsilon$. Then
--   $$
--   \sum_\chi|1-\chi(\mathrm{root})|^2H(\chi)\le4\Bigl(\varepsilon+\frac M{2K}\Bigr).
--   $$
--
--   Characters seeing the root translation are either detected at a sparse node or spread over many leaves.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/SparseActivity.lean#L261-L297

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

theorem OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.character_root_bound {A κ ν σ : Type*}
    [AddCommGroup A] [Fintype A] [Fintype κ] [Fintype ν] [Fintype σ]
    (H : AddChar A ℂ → ℝ) (root : A)
    (activeLeaf : κ → AddChar A ℂ → Prop) (bad : ν → AddChar A ℂ → Prop)
    (a : ν → σ → AddChar A ℂ → ℝ) (B : ν → ℝ) (C : κ → ℝ)
    (M ε K : ℝ) (hK : 0 < K) (hH : ∀ χ, 0 ≤ H χ)
    (hdense : ∀ χ, χ root ≠ 1 → (¬ ∃ v, bad v χ) →
      K ≤ ((Finset.univ.filter (fun u => activeLeaf u χ)).card : ℝ))
    (hleaf : ∀ u, 2 * (∑ χ, if activeLeaf u χ then H χ else 0) ≤ C u)
    (hleafBudget : (∑ u, C u) ≤ M)
    (ha : ∀ v s χ, 0 ≤ a v s χ)
    (hdetect : ∀ v χ, bad v χ → 1 ≤ ∑ s, a v s χ)
    (hcost : ∀ v, (∑ s, ∑ χ, a v s χ * H χ) ≤ B v)
    (hbudget : (∑ v, B v) ≤ ε) :
    (∑ χ : AddChar A ℂ, ‖1 - χ root‖ ^ 2 * H χ) ≤
      4 * (ε + M / (2 * K)) := by sorry
