-- Prove2me | Theorems.Thm_OAI_FiniteCircle_exists_disjoint_pair_subfamily
-- name    : OAI.FiniteCircle.exists_disjoint_pair_subfamily
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:14:02.325571+00:00
-- url     : https://prove2.me/theorems/949b1d3e-47d2-4438-b387-4bc53a946b48
-- title:
--   Two injections with $f(i)\ne g(i)$ on $I$ admit a cross-disjoint subfamily of at least $|I|/3$ indices
-- statement:
--   Let $\iota$ and $J$ be arbitrary types with decidable equality, and let $f,g:\iota\to J$ be two injective maps. Let $I\subseteq\iota$ be a finite set such that $f(i)\ne g(i)$ for every $i\in I$. Then there is a subset $S\subseteq I$ such that
--
--   $$
--   |I|\le 3\,|S|\qquad\text{and}\qquad f(i)\ne g(j)\ \text{ for all } i,j\in S,
--   $$
--
--   that is, $S$ contains at least a third of the elements of $I$, and the image sets $f(S)$ and $g(S)$ are disjoint.
--
--   Think of each $i\in I$ as a constraint linking the two positions $f(i)$ and $g(i)$ of $J$. The hypothesis only excludes constraints that link a position with itself; the conclusion extracts a large subfamily in which no position occurs both as a left end $f(i)$ and as a right end $g(j)$. Such constraints are independent of each other and therefore easy to count. This is how the lemma is used in the random construction of binary codes for edit-distance embeddings: when $J$ is finite, the bit assignments $\omega:J\to\{0,1\}$ with $\omega(f(i))=\omega(g(i))$ for all $i\in S$ are determined by their values outside $g(S)$, so there are at most $2^{|J|-|S|}\le 2^{|J|-|I|/3}$ of them.
--
--   **Formalization Note** $I$ is a `Finset` in a possibly infinite type $\iota$; no finiteness of $\iota$ or $J$ is assumed, and the cardinality inequality is stated in $\mathbb{N}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/BitCounting.lean#L11-L73

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

theorem OAI.FiniteCircle.exists_disjoint_pair_subfamily {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    (f g : ι → J) (hf : Function.Injective f) (hg : Function.Injective g)
    (I : Finset ι) (hne : ∀ i ∈ I, f i ≠ g i) :
    ∃ S ⊆ I, I.card ≤ 3*S.card ∧ ∀ i ∈ S, ∀ j ∈ S, f i ≠ g j := by sorry
