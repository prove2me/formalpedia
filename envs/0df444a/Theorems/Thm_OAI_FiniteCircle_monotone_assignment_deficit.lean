-- Prove2me | Theorems.Thm_OAI_FiniteCircle_monotone_assignment_deficit
-- name    : OAI.FiniteCircle.monotone_assignment_deficit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:10:47.67719+00:00
-- url     : https://prove2.me/theorems/007f25a4-8830-42d7-bc7e-7a99158403bf
-- title:
--   Deficit bound from a monotone letter-preserving assignment of positions
-- statement:
--   Let $x,y$ be words over an alphabet $\alpha$, with positions numbered from $0$. Let $\operatorname{lcs}(x,y)$ be the maximal length of a common subsequence and $\operatorname{def}(x,y)=|x|-\operatorname{lcs}(x,y)$ the deficit. Let $S\subseteq\{0,\dots,|x|-1\}$ be a set of positions of $x$ and let $f:\mathbb{N}\to\mathbb{N}$ satisfy:
--   - $f(i)<|y|$ for every $i\in S$;
--   - $f(i)\le f(i')$ whenever $i,i'\in S$ and $i\le i'$ ($f$ is weakly increasing on $S$);
--   - $x_i=y_{f(i)}$ for every $i\in S$.
--
--   Then
--   $$
--   \operatorname{def}(x,y)\ \le\ 2\bigl(|x|-|S|\bigr)+\#\bigl\{\,i\in S:\ i+1\in S\ \text{and}\ f(i)=f(i+1)\,\bigr\}.
--   $$
--
--   Thus a weakly increasing, letter-preserving assignment of positions of $x$ to positions of $y$ certifies a long common subsequence up to two kinds of defects: positions of $x$ that are not assigned (each costing at most $2$) and adjacent assigned positions sent to the same position of $y$ (each costing $1$). It is used to recover a common subsequence of two words from a matching between their encodings, by sending each block of one encoded word to the block containing the partner of a fixed offset.
--
--   **Formalization Note** The letter condition is stated with list indexing `x[i]` and `y[f i]`, whose bounds come from $S\subseteq\{0,\dots,|x|-1\}$ and the first hypothesis. The difference $|x|-|S|$ is a natural-number subtraction, which does not truncate because $|S|\le|x|$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/WindowMatching.lean#L258-L328

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

open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem OAI.FiniteCircle.monotone_assignment_deficit {α : Type*} {x y : List α}
    (S : Finset ℕ) (hS : S ⊆ Finset.range x.length) (f : ℕ → ℕ)
    (hf : ∀ i ∈ S, f i < y.length)
    (hm : ∀ i ∈ S, ∀ j ∈ S, i ≤ j → f i ≤ f j)
    (hl : ∀ i (hi : i ∈ S), x[i]'(Finset.mem_range.mp (hS hi)) = y[f i]'(hf i hi)) :
    deficit x y ≤ 2 * (x.length - S.card) +
      (S.filter (fun i => i+1 ∈ S ∧ f i = f (i+1))).card := by sorry
