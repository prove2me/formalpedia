-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_TreeDistortion_FiniteMass_finite_spectral_root_bound
-- name    : OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.finite_spectral_root_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:32:00.493669+00:00
-- url     : https://prove2.me/theorems/52f6f4ec-0984-4783-8312-535912af8e96
-- title:
--   Spectral root bound with translation tests
-- statement:
--   Let $A$ be a finite abelian group, $\widehat A$ its characters, and $H:\widehat A\to[0,\infty)$ a spectral mass. For an element $z$, $|1-\chi(z)|^2$ measures how much $\chi$ sees the translation by $z$; for a $\{0,1\}$-valued $f$ with $H=|\hat f|^2$, $\sum_\chi|1-\chi(z)|^2H(\chi)$ is the average of $|f(x+z)-f(x)|$. Assume the hypotheses of the cyclic-leaf root bound, except that bad characters are detected by translations: for each node $v$ there are shifts $\mathrm{shift}(v,s)\in A$, $s\in\sigma$ ($\sigma$ nonempty), such that
--   $$
--   |\sigma|\le\sum_s|1-\chi(\mathrm{shift}(v,s))|^2\quad\text{whenever }\chi\text{ is bad at }v,
--   $$
--   and each translation costs $\sum_\chi|1-\chi(\mathrm{shift}(v,s))|^2H(\chi)\le B_v$, with $\sum_vB_v\le\varepsilon$. Then $\sum_\chi|1-\chi(\mathrm{root})|^2H(\chi)\le4(\varepsilon+M/(2K))$.
--
--   This is the form used for the finite-tree words, where all tests are translations in the state group.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/SparseActivity.lean#L448-L483

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

theorem OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.finite_spectral_root_bound {A κ ν σ : Type*}
    [AddCommGroup A] [Fintype A] [Fintype κ] [Fintype ν]
    [Fintype σ] [Nonempty σ]
    (Q : κ → ℕ) [∀ u, NeZero (Q u)] (φ : ∀ u, ZMod (Q u) →+ A)
    (H : AddChar A ℂ → ℝ) (root : A) (bad : ν → AddChar A ℂ → Prop)
    (shift : ν → σ → A) (B : ν → ℝ) (C : κ → ℝ)
    (M ε K : ℝ) (hK : 0 < K) (hH : ∀ χ, 0 ≤ H χ)
    (hdense : ∀ χ, χ root ≠ 1 → (¬ ∃ v, bad v χ) →
      K ≤ ((Finset.univ.filter (fun u => χ (φ u 1) ≠ 1)).card : ℝ))
    (hleaf : ∀ u (z : ZMod (Q u)),
      (∑ χ, ‖1 - χ (φ u z)‖ ^ 2 * H χ) ≤ C u)
    (hleafBudget : (∑ u, C u) ≤ M)
    (hdetect : ∀ v χ, bad v χ →
      (Fintype.card σ : ℝ) ≤ ∑ s, ‖1 - χ (shift v s)‖ ^ 2)
    (hcost : ∀ v s, (∑ χ, ‖1 - χ (shift v s)‖ ^ 2 * H χ) ≤ B v)
    (hbudget : (∑ v, B v) ≤ ε) :
    (∑ χ : AddChar A ℂ, ‖1 - χ root‖ ^ 2 * H χ) ≤
      4 * (ε + M / (2 * K)) := by sorry
