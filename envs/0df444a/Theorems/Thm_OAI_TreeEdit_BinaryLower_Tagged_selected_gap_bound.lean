-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_Tagged_selected_gap_bound
-- name    : OAI.TreeEdit.BinaryLower.Tagged.selected_gap_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:10:52.90697+00:00
-- url     : https://prove2.me/theorems/39df5b93-9af3-45a0-a9fb-29e8cb47568c
-- title:
--   Large gaps in an increasing sequence consume its range
-- statement:
--   Let $v_0<v_1<\dots<v_n$ be natural numbers below $N$, let $S\subseteq\{0..n-1\}$, and $g\in\mathbb R$ with $v_{i+1}-v_i-1\ge g$ for $i\in S$. Then
--   $$
--   |S|\,g\le N-(n+1).
--   $$
--
--   The positions skipped by an increasing sequence of $n+1$ values below $N$ number at most $N-(n+1)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/TaggedGaps.lean#L23-L45

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Tagged
open Finset

theorem OAI.TreeEdit.BinaryLower.Tagged.selected_gap_bound {n N : ℕ} (v : Fin (n + 1) → ℕ)
    (hv : StrictMono v) (hN : ∀ i, v i < N) (S : Finset (Fin n))
    (g : ℝ) (hg : ∀ i ∈ S, g ≤ (v i.succ : ℝ) - (v i.castSucc : ℝ) - 1) :
    (S.card : ℝ) * g ≤ (N : ℝ) - (n + 1) := by sorry
