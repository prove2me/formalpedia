-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_Parameters_exists_finite_cap_parameters
-- name    : OAI.TreeEdit.BinaryLower.Parameters.exists_finite_cap_parameters
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:10:40.19393+00:00
-- url     : https://prove2.me/theorems/dab4d9bd-2287-4659-b45f-b60815a6ad2f
-- title:
--   Choosing the tree size for a given cap
-- statement:
--   Let $n(k)=(20k\cdot k^{20k})^{3k}$ be the binary word length. Let $c_0>0$ and $K\in\mathbb N$. There is $d_0$ such that every $d\ge d_0$ admits $k\ge\max(K,20)$ with $n(k)\le d$ and
--   $$
--   \exp\Bigl(\tfrac1{160}\sqrt{\log d\,\log\log d}\Bigr)\le c_0\Bigl(\frac k4\Bigr)^k .
--   $$
--
--   The source distortion $c_0(k/4)^k$ beats the target growth for the largest admissible $k$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteParameters.lean#L195-L218

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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteCoordinates
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteWordDetection
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CheapTranslations
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Distortion
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ParameterImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteParameters

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Parameters

theorem OAI.TreeEdit.BinaryLower.Parameters.exists_finite_cap_parameters {c₀ : ℝ} (hc₀ : 0 < c₀) (K : ℕ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∃ k : ℕ,
      K ≤ k ∧ 20 ≤ k ∧ finiteLength k ≤ d ∧
        Real.exp ((1 / 160 : ℝ) *
          Real.sqrt (Real.log (d : ℝ) * Real.log (Real.log (d : ℝ)))) ≤
            c₀ * ((k : ℝ) / 4) ^ k := by sorry
