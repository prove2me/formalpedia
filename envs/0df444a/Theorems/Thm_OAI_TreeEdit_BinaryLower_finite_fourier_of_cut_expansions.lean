-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_finite_fourier_of_cut_expansions
-- name    : OAI.TreeEdit.BinaryLower.finite_fourier_of_cut_expansions
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:40:23.966088+00:00
-- url     : https://prove2.me/theorems/890827db-9fa3-4a9c-9ae3-4291c6e07718
-- title:
--   Fourier representation of translation averages from cut expansions
-- statement:
--   Let $A$ be a finite abelian group, $F:A\to E$ a map into a normed group, and $U_c:A\to\mathbb R$ indexed by a finite set, with weights $a_c\ge0$ and
--   $$
--   \|F(x)-F(y)\|=\sum_ca_c\,|U_c(x)-U_c(y)| .
--   $$
--   Suppose each $U_c$ satisfies $\mathbb E_x|U_c(x+z)-U_c(x)|=\sum_\chi|1-\chi(z)|^2b_c(\chi)$ with $b_c\ge0$. Then there is $H\ge0$ on characters with $\mathbb E_x\|F(x+z)-F(x)\|=\sum_\chi|1-\chi(z)|^2H(\chi)$ for all $z$.
--
--   Spectral representations of translation averages are closed under nonnegative combinations.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteFourierAssembly.lean#L41-L75

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open scoped BigOperators

theorem OAI.TreeEdit.BinaryLower.finite_fourier_of_cut_expansions
    {A C E : Type*} [AddCommGroup A] [Fintype A] [Fintype C]
    [NormedAddCommGroup E]
    (F : A → E) (a : C → ℝ) (U : C → A → ℝ)
    (b : C → AddChar A ℂ → ℝ)
    (ha : ∀ c, 0 ≤ a c) (hb : ∀ c χ, 0 ≤ b c χ)
    (hcut : ∀ x y, ‖F x - F y‖ = ∑ c, a c * |U c x - U c y|)
    (hfourier : ∀ c z,
      (𝔼 x, |U c (x + z) - U c x|) =
        ∑ χ : AddChar A ℂ, ‖1 - χ z‖ ^ 2 * b c χ) :
    ∃ H : AddChar A ℂ → ℝ, (∀ χ, 0 ≤ H χ) ∧
      ∀ z, (𝔼 x, ‖F (x + z) - F x‖) =
        ∑ χ : AddChar A ℂ, ‖1 - χ z‖ ^ 2 * H χ := by sorry
