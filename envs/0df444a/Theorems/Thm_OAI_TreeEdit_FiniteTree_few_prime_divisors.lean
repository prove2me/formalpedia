-- Prove2me | Theorems.Thm_OAI_TreeEdit_FiniteTree_few_prime_divisors
-- name    : OAI.TreeEdit.FiniteTree.few_prime_divisors
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:50:47.443286+00:00
-- url     : https://prove2.me/theorems/de409fa6-1cd9-43a4-b33f-dd171062de49
-- title:
--   A nonzero integer with $|d|<b^s$ is divisible by fewer than $s$ of any distinct primes that are at least $b$
-- statement:
--   Let $p_0,\dots,p_{m-1}$ be pairwise distinct primes, let $b\ge1$ be a natural number with $p_i\ge b$ for every $i$, and let $s,T$ be natural numbers with $T\le b^{s}$. If $d$ is a nonzero integer with $|d|<T$, then fewer than $s$ of the primes divide $d$:
--
--   $$
--   \#\{\,i\in\{0,\dots,m-1\}:\ p_i\mid d\,\}<s.
--   $$
--
--   Taking $T=b^s$, this holds for every nonzero integer $d$ with $|d|<b^s$. In the circle construction the primes are the ones selected by a permutation, and the statement guarantees that a small nonzero integer (such as a difference of shifts) is not divisible by many of them.
--
--   **Formalization Note** The primes are an injective map `p : Fin m → ℕ` with `Nat.Prime (p i)`; divisibility is taken in $\mathbb Z$ and $|d|$ is `d.natAbs`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/TreeArithmetic.lean#L20-L40

import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic

open OAI OAI.TreeEdit OAI.TreeEdit.FiniteTree
universe u
attribute [local instance] Classical.propDecidable

theorem OAI.TreeEdit.FiniteTree.few_prime_divisors {m b s T : ℕ} (p : Fin m → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (hb : 1 ≤ b) (hpb : ∀ i, b ≤ p i) (hT : T ≤ b ^ s)
    (d : ℤ) (hd : d ≠ 0) (hdT : d.natAbs < T) :
    (Finset.univ.filter (fun i => (p i : ℤ) ∣ d)).card < s := by sorry
