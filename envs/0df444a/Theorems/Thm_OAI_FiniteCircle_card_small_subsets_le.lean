-- Prove2me | Theorems.Thm_OAI_FiniteCircle_card_small_subsets_le
-- name    : OAI.FiniteCircle.card_small_subsets_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:14:36.286504+00:00
-- url     : https://prove2.me/theorems/736338b0-d2f0-4812-b2a8-a6293c6cc89f
-- title:
--   At most $e^{w/512}$ subsets of a $w$-element set have at most $w/2^{20}$ elements
-- statement:
--   Let $w$ be a natural number and $[w]=\{0,1,\dots,w-1\}$. Then the number of subsets of $[w]$ with at most $w/2^{20}$ elements is at most $e^{w/512}$:
--
--   $$
--   \#\Bigl\{S\subseteq[w]\ :\ |S|\le \frac{w}{2^{20}}\Bigr\}\ \le\ e^{w/512}.
--   $$
--
--   Here $2^{20}=1048576$, and the size condition is an inequality between real numbers (no rounding of $w/2^{20}$).
--
--   The bound says that very sparse subsets are exponentially rare among all $2^{w}$ subsets, with an explicit small exponent. In the random construction of binary codes for edit-distance embeddings it controls the number of nearly contiguous increasing lists of positions in a codeword of length $w$: such a list is determined by its first and last positions together with the set of at most $w/2^{20}$ skipped positions in between, so there are at most $w^{2}e^{w/512}$ of them. This count is small compared with the factor $2^{-w/64}$ by which each potential bad matching cuts down the number of admissible codes in the union bound used there.
--
--   **Formalization Note** The subsets are the elements of `Finset (Fin w)`, and their number is compared with `Real.exp (w/512)` after casting to $\mathbb{R}$. For $w=0$ both sides equal $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/BitCounting.lean#L117-L151

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

open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem OAI.FiniteCircle.card_small_subsets_le (w : ℕ) :
    ((Finset.univ.filter (fun S : Finset (Fin w) => (S.card : ℝ) ≤ (w : ℝ)/1048576)).card : ℝ) ≤
      Real.exp ((w : ℝ)/512) := by sorry
