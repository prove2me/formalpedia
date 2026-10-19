-- Prove2me | Theorems.Thm_OAI_FiniteCircle_StandingPrimes_mask_alphabet_bound
-- name    : OAI.FiniteCircle.StandingPrimes.mask_alphabet_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:58:08.765425+00:00
-- url     : https://prove2.me/theorems/8c1dd04d-70f4-4308-ab47-11edb54ff114
-- title:
--   The level-$h$ mask alphabet has at most $h^{6h^2}$ letters
-- statement:
--   A *standing prime array* for $h$ is a function $p\colon\mathbb N\times\mathbb N\to\mathbb N$, $(l,s)\mapsto p_{l,s}$, such that (i) for $1\le l\le h$ and $0\le s<h$ the number $p_{l,s}$ is prime with $h^3<p_{l,s}\le 2h^3$; (ii) these $h^2$ primes are pairwise distinct; (iii) $p_{l,s}=1$ for every other pair $(l,s)$.
--
--   For $l\ge1$ the *mask tags* of level $l$ are the pairs $T_l=\{(s,b):0\le s<h,\ 0\le b<p_{l,s}\}$, so $|T_l|=\sum_{s<h}p_{l,s}$. The *mask alphabets* are $\mathcal A_0=\{0,1\}$ and $\mathcal A_{l}=T_{l}\times\mathcal A_{l-1}$ for $l\ge1$.
--
--   Let $h\ge2$ and let $p$ be a standing prime array for $h$. Then
--
--   $$
--   |\mathcal A_h|\;\le\;h^{6h^2}.
--   $$
--
--   The letters of the level-$h$ mask words are the elements of $\mathcal A_h$. The bound controls the block length of a binary code for this alphabet: a code of the kind used in the construction has block length $w\le C\ln(2|\mathcal A_h|)=O(h^2\ln h)$, which keeps the encoded mask words short enough for the final length budget.
--
--   **Formalization Note** The alphabet is `MaskAlphabet h p h`, built from `MaskTag h p l = Σ k : Fin h, Fin (p l k)`, and $|\cdot|$ is `Fintype.card`. The hypothesis on $p$ is the structure `StandingPrimes h p`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Parameters.lean#L101-L118

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

theorem OAI.FiniteCircle.StandingPrimes.mask_alphabet_bound {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2≤h) :
    Fintype.card (MaskAlphabet h p h) ≤ h^(6*h^2) := by sorry
