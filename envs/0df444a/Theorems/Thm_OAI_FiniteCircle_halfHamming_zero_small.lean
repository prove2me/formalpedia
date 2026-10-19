-- Prove2me | Theorems.Thm_OAI_FiniteCircle_halfHamming_zero_small
-- name    : OAI.FiniteCircle.halfHamming_zero_small
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:32:10.70652+00:00
-- url     : https://prove2.me/theorems/6f9fe916-d238-42c5-bf46-b080565632ce
-- title:
--   For even $M$ and $0\le v\le M/2$, the half-circle indicators at $0$ and $v$ differ at exactly $2v$ points
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
--   **Theorem.** Assume that $M$ is even, and let $v\in\mathbb{Z}/M\mathbb{Z}$ have representative $r\in\{0,\dots,M-1\}$ with $r\le M/2$. Then
--   $$
--   H(0,v)=2r .
--   $$
--
--   Moving a half circle forward by $r\le M/2$ steps loses $r$ points at its beginning and gains $r$ points at its end. This is the base computation behind the identity $H(v,w)=2\|w-v\|_M$, where $\|x\|_M$ is the circular distance from $x$ to $0$; it gives the exact Hamming distance between two bottom-level words of the hard-word constructions.
--
--   **Formalization Note** The indicator is `halfBit v b = decide ((b - v).val < M/2)` and the distance is `halfHamming v w`, the cardinality of the finset of disagreements; `M` carries a `NeZero` instance. Evenness is the hypothesis `M = 2*(M/2)`, and the bound on `v` is `v.val <= M/2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/CircleWords.lean#L308-L353

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

theorem OAI.FiniteCircle.halfHamming_zero_small {M : ℕ} [NeZero M] (he : M = 2*(M/2))
    (v : ZMod M) (hv : v.val ≤ M/2) : halfHamming 0 v = 2*v.val := by sorry
