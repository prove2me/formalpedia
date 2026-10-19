-- Prove2me | Theorems.Thm_OAI_FiniteCircle_editDistance_ofFn_le_hamming
-- name    : OAI.FiniteCircle.editDistance_ofFn_le_hamming
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:52:03.505405+00:00
-- url     : https://prove2.me/theorems/a5739e70-8d53-44ad-8cf9-991484c29290
-- title:
--   Edit distance between two words of equal length is at most their Hamming distance
-- statement:
--   Let $\alpha$ be an alphabet with decidable equality. For finite words $x,y$ over $\alpha$, the *edit distance* $\operatorname{ed}(x,y)$ is the least number of single-letter insertions, deletions and substitutions needed to transform $x$ into $y$.
--
--   Let $N\ge 0$ and let $f,g\colon\{0,1,\dots,N-1\}\to\alpha$ be arbitrary maps, read as the words $f(0)f(1)\cdots f(N-1)$ and $g(0)g(1)\cdots g(N-1)$ of length $N$. Then
--
--   $$
--   \operatorname{ed}\bigl(f(0)f(1)\cdots f(N-1),\; g(0)g(1)\cdots g(N-1)\bigr)\;\le\;\#\{\,i\in\{0,\dots,N-1\} : f(i)\neq g(i)\,\}.
--   $$
--
--   In words, the edit distance between two words of the same length never exceeds their Hamming distance, because every mismatched position can be repaired by one substitution. This elementary comparison is used to bound edit distances of explicitly indexed words by coordinatewise counts, for instance for the half-circle indicator words $b\mapsto\mathbf 1[(b-v)\bmod M<M/2]$ on $\mathbb Z/M\mathbb Z$, whose Hamming distances can be computed exactly.
--
--   **Formalization Note** The two words are `List.ofFn f` and `List.ofFn g` for `f g : Fin N → α`, and the right-hand side is the cardinality of `Finset.univ.filter fun i => f i ≠ g i`. The edit distance `editDistance x y` is the infimum of all `n` for which there is an edit script `EditScript n x y`, i.e. a chain of `n` single insert, delete or substitute steps.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Translations.lean#L36-L60

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

open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem OAI.FiniteCircle.editDistance_ofFn_le_hamming {α : Type*} [DecidableEq α] {N : ℕ} (f g : Fin N → α) :
    editDistance (List.ofFn f) (List.ofFn g) ≤
      (Finset.univ.filter fun i => f i ≠ g i).card := by sorry
