-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_PrimeSupply_finite_tree_prime_family
-- name    : OAI.TreeEdit.BinaryLower.PrimeSupply.finite_tree_prime_family
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:16:15.918188+00:00
-- url     : https://prove2.me/theorems/8cec78cc-fc71-48b7-a35e-2a3c6876d127
-- title:
--   Distinct primes for every level and child of the tree
-- statement:
--   There is $k_0$ such that for every $k\ge k_0$ there is an injective map
--   $$
--   p:\{1..k\}\times\{1..20k\}\to\mathbb N
--   $$
--   whose values are primes with $k^4\le p(q,i)\le k^5$.
--
--   Every level-child pair of the tree receives its own prime of size about $k^4$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/PrimeSupply.lean#L132-L150

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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EncodedImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFamilyTransfer

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open Filter Finset
open scoped Topology

theorem OAI.TreeEdit.BinaryLower.PrimeSupply.finite_tree_prime_family :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ p : (Fin k × Fin (20 * k)) ↪ ℕ,
        ∀ ji, Nat.Prime (p ji) ∧ k ^ 4 ≤ p ji ∧ p ji ≤ k ^ 5 := by sorry
