-- Prove2me | Theorems.Thm_OAI_FiniteCircle_exists_separating_scale
-- name    : OAI.FiniteCircle.exists_separating_scale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:24:59.72857+00:00
-- url     : https://prove2.me/theorems/01f0ab91-b40e-45d5-a554-754daff68203
-- title:
--   Every $1\le q\le m$ admits a dyadic scale $2^k\le m$ with $q\le4\cdot2^k$ and $2\cdot2^k\le q+1$
-- statement:
--   **Theorem.** Let $m$ and $q$ be natural numbers with $0<q\le m$. Then there is an integer $k$ with $0\le k\le\lfloor\log_2m\rfloor$ such that
--
--   $$
--   1\le2^{k}\le m,\qquad q\le4\cdot2^{k},\qquad 2\cdot2^{k}\le q+1 .
--   $$
--
--   In other words, among the dyadic scales $s=2^{k}\le m$ there is one with $q/4\le s\le(q+1)/2$. In the recursive histogram embedding of edit distance, windows are taken at all dyadic scales $s=2^{k}$ with $k\le\lfloor\log_2m\rfloor$. When two blocks of length $m$ have deficit $q$, this lemma selects a scale that is small enough ($2s\le q+1$) for every pair of windows of length $m-s+1$ cut from the two blocks to still have deficit at least $s$, and large enough ($q\le4s$) for the resulting lower bound $s$ on the expected histogram distance to recover a quarter of the deficit.
--
--   **Formalization Note** The scale index $k$ is an element of `Fin (Nat.log 2 m + 1)`, where `Nat.log 2 m` is $\lfloor\log_2m\rfloor$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Separation.lean#L81-L101

import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Distortion
import Definitions.Def_OAI_Combinatorics_FiniteCircle_BlockMatching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_OffsetRecovery
import Definitions.Def_OAI_Combinatorics_FiniteCircle_RandomCodes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Codes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Lower
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Windows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Partitions
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Histograms
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Separation

open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem OAI.FiniteCircle.exists_separating_scale {m q : ℕ} (hq : 0 < q) (hqm : q ≤ m) :
    ∃ k : Fin (Nat.log 2 m + 1), 1 ≤ 2^k.val ∧ 2^k.val ≤ m ∧
      q ≤ 4 * 2^k.val ∧ 2 * 2^k.val ≤ q+1 := by sorry
