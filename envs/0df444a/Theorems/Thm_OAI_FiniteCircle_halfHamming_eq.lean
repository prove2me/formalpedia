-- Prove2me | Theorems.Thm_OAI_FiniteCircle_halfHamming_eq
-- name    : OAI.FiniteCircle.halfHamming_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:33:18.937815+00:00
-- url     : https://prove2.me/theorems/36cdf48f-3343-4c5d-8501-1b561183aa80
-- title:
--   For even $M$, half-circle indicators differ at exactly twice the circular distance of their starting points
-- statement:
--   Let $M\ge1$ and identify each residue $b\in\mathbb{Z}/M\mathbb{Z}$ with its representative in $\{0,1,\dots,M-1\}$. For $v\in\mathbb{Z}/M\mathbb{Z}$ the half-circle indicator $\chi_v:\mathbb{Z}/M\mathbb{Z}\to\{0,1\}$ is
--   $$
--   \chi_v(b)=\begin{cases}1 & \text{if the representative of } b-v \text{ is less than } \lfloor M/2\rfloor,\\ 0 & \text{otherwise,}\end{cases}
--   $$
--   the indicator of the arc $A_v=\{v,v+1,\dots,v+\lfloor M/2\rfloor-1\}$ of $\lfloor M/2\rfloor$ consecutive residues starting at $v$. The half-Hamming distance of $v,w\in\mathbb{Z}/M\mathbb{Z}$ is the number of residues at which the two indicators differ,
--   $$
--   H(v,w)=\#\{b\in\mathbb{Z}/M\mathbb{Z}:\ \chi_v(b)\neq\chi_w(b)\}=|A_v\,\triangle\,A_w| .
--   $$
--
--   For $x\in\mathbb{Z}/M\mathbb{Z}$ let $\|x\|_M$ be the circular distance from $x$ to $0$, the least $|s|$ over integers $s\equiv x\pmod M$.
--
--   **Theorem.** Assume that $M$ is even. Then for all $v,w\in\mathbb{Z}/M\mathbb{Z}$,
--   $$
--   H(v,w)=2\,\|w-v\|_M .
--   $$
--
--   Thus the Hamming distance between two half-circle indicator words is an exact multiple of the circular distance between their starting points, which in turn equals $M$ times the distance of $(w-v)/M$ to the nearest integer. The bottom-level words of the hard-word constructions are such indicator words, and this identity, combined with the comparison of Hamming distance and deficit for step words, bounds their deficit from below by a constant times the circular distance of the corresponding phases.
--
--   **Formalization Note** The indicator is `halfBit v b = decide ((b - v).val < M/2)` and the distance is `halfHamming v w`, the cardinality of the finset of disagreements; `M` carries a `NeZero` instance. Evenness is the hypothesis `M = 2*(M/2)`, and the circular distance is `(w - v).valMinAbs.natAbs`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/CircleWords.lean#L355-L372

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

theorem OAI.FiniteCircle.halfHamming_eq {M : ℕ} [NeZero M] (he : M = 2*(M/2))
    (v w : ZMod M) : halfHamming v w = 2*(w-v).valMinAbs.natAbs := by sorry
