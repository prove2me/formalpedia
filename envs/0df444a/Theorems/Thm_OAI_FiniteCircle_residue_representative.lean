-- Prove2me | Theorems.Thm_OAI_FiniteCircle_residue_representative
-- name    : OAI.FiniteCircle.residue_representative
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:54:09.521619+00:00
-- url     : https://prove2.me/theorems/c31369ef-91b2-4b6b-8076-48bd123cb1e4
-- title:
--   Chinese remainder theorem with a representative below the product of the moduli
-- statement:
--   Let $h\ge 0$ and let $p_0,\dots,p_{h-1}$ be positive integers that are pairwise coprime, i.e. $\gcd(p_i,p_j)=1$ whenever $i\neq j$. Then every family of residues $z_k\in\mathbb Z/p_k\mathbb Z$ ($0\le k<h$) has a simultaneous representative among the natural numbers below $\prod_k p_k$: there is $q\in\mathbb N$ with
--
--   $$
--   q<\prod_{k=0}^{h-1}p_k\qquad\text{and}\qquad q\equiv z_k \pmod{p_k}\quad\text{for all }0\le k<h .
--   $$
--
--   This is the existence part of the Chinese remainder theorem in a form convenient for indexing: any prescribed tuple of phases modulo the $p_k$ is realized by a single integer shift $q$ that is smaller than the common period $\prod_k p_k$. In the circle-word construction it shows that adding a level phase vector to a state has the same effect as shifting the row index by such a $q$.
--
--   **Formalization Note** The residues form a dependent function `z : ∀ k, ZMod (p k)`, and the congruence is stated as the equality `(q : ZMod (p k)) = z k` in $\mathbb Z/p_k\mathbb Z$. For $h=0$ the product is $1$ and $q=0$ works.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Translations.lean#L266-L280

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

theorem OAI.FiniteCircle.residue_representative {h : ℕ} (p : Fin h → ℕ)
    (hn : ∀ k, 0 < p k) (hp : Pairwise (fun i j => Nat.Coprime (p i) (p j)))
    (z : ∀ k, ZMod (p k)) : ∃ q : ℕ, q < ∏ k, p k ∧ ∀ k, (q : ZMod (p k)) = z k := by sorry
