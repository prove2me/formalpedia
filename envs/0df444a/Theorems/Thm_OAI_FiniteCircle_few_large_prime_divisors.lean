-- Prove2me | Theorems.Thm_OAI_FiniteCircle_few_large_prime_divisors
-- name    : OAI.FiniteCircle.few_large_prime_divisors
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:49:09.10099+00:00
-- url     : https://prove2.me/theorems/28e3255e-e95a-4e8d-b52b-09cb6562421c
-- title:
--   Fewer than $h/3$ primes of size at least $h^3$ divide a nonzero integer of absolute value below $h^h$
-- statement:
--   Let $h\ge2$ be an integer and let $(p_i)_{i\in\iota}$ be a finite family of pairwise distinct primes with $p_i\ge h^3$ for every $i$. Let $\beta$ be a nonzero integer with $|\beta|<h^h$. Then
--
--   $$
--   3\cdot\#\{i\in\iota:\ p_i\mid\beta\}<h .
--   $$
--
--   In the branching arguments for annihilating characters, $\beta$ is the integer frequency sum at a node of a tree and the $p_i$ are the $h$ primes of one level; the lemma guarantees that more than two thirds of these primes do not divide $\beta$, which forces many children with nonzero frequency sum.
--
--   **Formalization Note** The family is a function `p : ι → ℕ` on a finite type, assumed injective, with `Nat.Prime (p i)` and `h ^ 3 ≤ p i`; $|\beta|$ is `β.natAbs`, and divisibility is taken in $\mathbb{Z}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/MaskBranching.lean#L11-L37

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

open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem OAI.FiniteCircle.few_large_prime_divisors {h : ℕ} (hh : 2 ≤ h)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (hlarge : ∀ i, h ^ 3 ≤ p i) {β : ℤ} (hβ : β ≠ 0)
    (hsmall : β.natAbs < h ^ h) :
    3 * ((Finset.univ.filter fun i => (p i : ℤ) ∣ β).card) < h := by sorry
