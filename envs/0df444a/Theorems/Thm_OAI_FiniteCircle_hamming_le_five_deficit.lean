-- Prove2me | Theorems.Thm_OAI_FiniteCircle_hamming_le_five_deficit
-- name    : OAI.FiniteCircle.hamming_le_five_deficit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:30:26.17256+00:00
-- url     : https://prove2.me/theorems/40107519-23c0-4b4c-84e7-078ccc11bbf1
-- title:
--   Hamming distance to a binary word with at most two switch points is at most five times the deficit
-- statement:
--   Let $n\in\mathbb{N}$ and let $f=f_0f_1\cdots f_{n-1}$ and $g=g_0g_1\cdots g_{n-1}$ be binary words of length $n$. Let $\operatorname{lcs}(f,g)$ be the length of a longest common subsequence of $f$ and $g$ and $\operatorname{def}(f,g)=n-\operatorname{lcs}(f,g)$ their deficit. Let $t,u\in\mathbb{N}$ be two thresholds and assume that $g$ can change its value only across a threshold: for all positions $i,j<n$,
--   $$
--   g_i\neq g_j\ \Longrightarrow\ \min(i,j)<t\le\max(i,j)\ \text{ or }\ \min(i,j)<u\le\max(i,j).
--   $$
--   Equivalently, $g$ is constant on each of the (at most three) intervals into which the thresholds $t$ and $u$ cut $\{0,1,\dots,n-1\}$.
--
--   **Theorem.** Under this hypothesis,
--   $$
--   \#\{i<n:\ f_i\neq g_i\}\le5\operatorname{def}(f,g).
--   $$
--
--   For general words the Hamming distance can be far larger than the deficit (a cyclic shift by one position), but not when one of the words is a step word with two switch points. The theorem is applied to indicator words of arcs of a cycle, whose Hamming distance is known exactly, to obtain a lower bound on the deficit of two such words in terms of the distance between the arcs.
--
--   **Formalization Note** The words are functions `f g : Fin n -> Bool` turned into lists by `List.ofFn`, and the Hamming distance is the cardinality of the finset of positions at which `f` and `g` differ. The thresholds `t` and `u` are arbitrary natural numbers and may exceed `n`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/CircleWords.lean#L167-L218

import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords

open OAI OAI.FiniteCircle
open scoped BigOperators List

theorem OAI.FiniteCircle.hamming_le_five_deficit {n : ℕ} (f g : Fin n → Bool) (t u : ℕ)
    (hg : ∀ i j : Fin n, g i ≠ g j →
      (i.val < t ∧ t ≤ j.val) ∨ (j.val < t ∧ t ≤ i.val) ∨
      (i.val < u ∧ u ≤ j.val) ∨ (j.val < u ∧ u ≤ i.val)) :
    (Finset.univ.filter (fun i => f i ≠ g i)).card ≤
      5*deficit (List.ofFn f) (List.ofFn g) := by sorry
