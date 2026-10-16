-- Prove2me | Theorems.Thm_OAI_TreeEdit_TorusFourier_sum_chord_detect
-- name    : OAI.TreeEdit.TorusFourier.sum_chord_detect
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:07:27.254765+00:00
-- url     : https://prove2.me/theorems/5b63fcbc-7159-447a-976c-76dada9fbd65
-- title:
--   Characters of $\mathbb{Z}/JQ$ with centered frequency at least $Q$ are detected by the first $J$ shifts
-- statement:
--   Let $M, Q, J$ be natural numbers with $M \ge 1$, $Q > 0$ and $M = JQ$. Every additive character $\chi$ of $\mathbb{Z}/M$ (a map $\chi : \mathbb{Z}/M \to \mathbb{C}$ with $\chi(0) = 1$ and $\chi(x+y) = \chi(x)\chi(y)$) has the form $\chi(u) = e^{2\pi i k \bar u/M}$ for a unique frequency $k \in \mathbb{Z}/M$, where $\bar u \in \{0,\dots,M-1\}$ is the standard representative of $u$. Let $\tilde k \in \mathbb{Z}$ be the centered representative of $k$, i.e. $\tilde k \equiv k \pmod M$ and $-M < 2\tilde k \le M$.
--
--   **Theorem.** If $|\tilde k| \ge Q$, then
--
--   $$
--   J \le \sum_{a=0}^{J-1} \Big(2 - 2\,\mathrm{Re}\,\chi(a+1)\Big).
--   $$
--
--   Since $2 - 2\,\mathrm{Re}\,\chi(u) = |1-\chi(u)|^2$, the multiplier of a character whose centered frequency is at least $Q$ in absolute value has average at least $1$ over the shifts $1, 2, \dots, J$. This is how high-frequency characters are detected by small shifts (of at most $J = M/Q$ grid steps), whose edit cost is small.
--
--   **Formalization Note** The frequency is the preimage of $\chi$ under Mathlib's isomorphism `AddChar.zmodAddEquiv`, its centered representative is `ZMod.valMinAbs` (the definition `centered`), and $a + 1$ is the cast of the natural number $a + 1$ into `ZMod M`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/CircleFourier.lean#L72-L106

import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleFourier

open OAI OAI.TreeEdit OAI.TreeEdit.TorusFourier
open scoped BigOperators
open Classical

theorem OAI.TreeEdit.TorusFourier.sum_chord_detect {M Q J : ℕ} [NeZero M] (hQ : 0 < Q) (hM : M = J * Q)
    (χ : AddChar (ZMod M) ℂ) (hχ : (Q : ℝ) ≤ |(centered χ : ℝ)|) :
    (J : ℝ) ≤ ∑ a ∈ Finset.range J, (2 - 2 * (χ (a + 1)).re) := by sorry
