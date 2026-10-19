-- Prove2me | Theorems.Thm_OAI_FiniteCircle_StandingPrimes_mask_alphabet_ge
-- name    : OAI.FiniteCircle.StandingPrimes.mask_alphabet_ge
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:59:16.382375+00:00
-- url     : https://prove2.me/theorems/61711b28-0293-43f1-b97d-f2f25aeda410
-- title:
--   Every mask alphabet has at least two letters
-- statement:
--   A *standing prime array* for $h$ is a function $p\colon\mathbb N\times\mathbb N\to\mathbb N$, $(l,s)\mapsto p_{l,s}$, such that (i) for $1\le l\le h$ and $0\le s<h$ the number $p_{l,s}$ is prime with $h^3<p_{l,s}\le 2h^3$; (ii) these $h^2$ primes are pairwise distinct; (iii) $p_{l,s}=1$ for every other pair $(l,s)$.
--
--   For every $l\ge1$ the *mask tags* of level $l$ are the pairs $T_l=\{(s,b):0\le s<h,\ 0\le b<p_{l,s}\}$, and the *mask alphabets* are $\mathcal A_0=\{0,1\}$ and $\mathcal A_{l}=T_{l}\times\mathcal A_{l-1}$ for $l\ge1$ (defined for all levels, also beyond $h$).
--
--   Let $h\ge1$ and let $p$ be a standing prime array for $h$. Then for every $l\in\mathbb N$,
--
--   $$
--   |\mathcal A_l|\;\ge\;2 .
--   $$
--
--   The binary codes used to encode mask words are constructed for finite alphabets with at least two letters, so this lemma makes those code constructions applicable to the mask alphabet at level $h$.
--
--   **Formalization Note** The alphabet is `MaskAlphabet h p l` and $|\cdot|$ is `Fintype.card`; the statement holds for every natural number `l`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Parameters.lean#L135-L148

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

theorem OAI.FiniteCircle.StandingPrimes.mask_alphabet_ge {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 1≤h) (l : ℕ) : 2≤Fintype.card (MaskAlphabet h p l) := by sorry
