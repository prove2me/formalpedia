-- Prove2me | Theorems.Thm_OAI_FiniteCircle_halfHamming_translate
-- name    : OAI.FiniteCircle.halfHamming_translate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:31:34.979768+00:00
-- url     : https://prove2.me/theorems/921b46ae-223a-4d15-ad6f-f5d4b81d97b1
-- title:
--   The Hamming distance between half-circle indicators is invariant under rotation
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
--   **Theorem.** For all $v,w,a\in\mathbb{Z}/M\mathbb{Z}$,
--   $$
--   H(v+a,\ w+a)=H(v,w).
--   $$
--
--   Rotating both arcs by the same amount does not change how much they disagree. This reduces the computation of $H(v,w)$ to the case $v=0$, which is how the exact formula $H(v,w)=2\|w-v\|_M$ for even $M$ is obtained, where $\|x\|_M$ denotes the circular distance from $x$ to $0$ (the least $|s|$ over integers $s\equiv x\pmod M$). The half-circle indicators are the binary words at the bottom level of the recursive hard-word constructions.
--
--   **Formalization Note** The indicator is `halfBit v b = decide ((b - v).val < M/2)` and the distance is `halfHamming v w`, the cardinality of the finset of disagreements; `M` carries a `NeZero` instance.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/CircleWords.lean#L283-L300

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

theorem OAI.FiniteCircle.halfHamming_translate {M : ℕ} [NeZero M] (v w a : ZMod M) :
    halfHamming (v+a) (w+a) = halfHamming v w := by sorry
