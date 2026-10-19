-- Prove2me | Theorems.Thm_OAI_FiniteCircle_recursive_length_bound
-- name    : OAI.FiniteCircle.recursive_length_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:57:04.301634+00:00
-- url     : https://prove2.me/theorems/34e1b039-7147-407f-a305-3a5311b2b9c3
-- title:
--   Recursive length bound $L_l\le M\,h^{8hl}$ for levels $l\le h$
-- statement:
--   Let $h,M\in\mathbb N$ with $h\ge3$, and let $P,T,L\colon\mathbb N\to\mathbb N$ (written $l\mapsto P_l,T_l,L_l$) satisfy
--
--   - $L_0=M$ and $L_{l+1}=\bigl(h^{2h}P_{l+1}\bigr)\bigl(T_{l+1}L_l\bigr)$ for every $l\ge0$;
--   - $P_l\le h^{4h}$ and $T_l\le h^5$ for every $l$ with $1\le l\le h$.
--
--   Then for every $l\le h$,
--
--   $$
--   L_l\;\le\;M\,h^{8hl}.
--   $$
--
--   In the circle-word construction the length of a level-$l$ word obeys exactly this recursion: level $l+1$ repeats $h^{2h}P_{l+1}$ rows, where $P_{l+1}$ is a product of $h$ primes of size at most $h^4$, and each row consists of $T_{l+1}$ tagged copies of level-$l$ words. The lemma is applied both to the mask words and to the excluded-residue words; with $M$ the circle size it gives polynomial-in-$M$ control of the final word length at level $h$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Parameters.lean#L60-L76

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

open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem OAI.FiniteCircle.recursive_length_bound (h M : ℕ) (P T L : ℕ → ℕ) (hh : 3≤h)
    (h0 : L 0=M) (hs : ∀ l, L (l+1)=(h^(2*h)*P (l+1))*(T (l+1)*L l))
    (hP : ∀ l, 1≤l → l≤h → P l≤h^(4*h))
    (hT : ∀ l, 1≤l → l≤h → T l≤h^5) :
    ∀ l, l≤h → L l ≤ M*h^(8*h*l) := by sorry
