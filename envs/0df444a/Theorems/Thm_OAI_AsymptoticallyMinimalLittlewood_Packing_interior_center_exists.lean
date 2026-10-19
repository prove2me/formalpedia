-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_interior_center_exists
-- name    : OAI.AsymptoticallyMinimalLittlewood.Packing.interior_center_exists
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:29:21.283338+00:00
-- url     : https://prove2.me/theorems/138c9024-b8a0-488b-ba0c-4193eb50c867
-- title:
--   Every interior site of a chunk is a slot center for some period and shift
-- statement:
--   Let $r\ge1$ and $d:\{0,\dots,r-1\}\to\mathbb N$. The odd slot lengths are $L_i=2d_i+1$, the period length is $P=\sum_{i<r}L_i$, and the prefix of slot $i$ is $\pi_i=\sum_{j<i}L_j$, so that slot $i$ occupies the positions $\pi_i+1,\dots,\pi_i+L_i$ of a period and has central position $\pi_i+d_i+1$.
--
--   **Theorem.** Let $R,t$ be natural numbers with $t<(R-2)P$, and let $i$ be a slot. Then there exist natural numbers $p$ and $s$ with $p+1<R$ and $s<P$ such that
--
--   $$
--   pP+s+\pi_i+d_i+1=P+1+t .
--   $$
--
--   The left-hand side is the center of slot $i$ in period $p$ after a shift by $s$, measured from the start of a chunk consisting of $R$ periods. Hence every interior site $P+1+t$ of the chunk, i.e. every site from $P+1$ to $(R-1)P$ (excluding the first and the last period), is the center of slot $i$ for some admissible period index $p\le R-2$ and some shift $s\in\{0,\dots,P-1\}$. This links each interior site of a chunk to a slot-center position, which is how fixed residues are related to the random shifts in the slot construction.
--
--   **Formalization Note** The quantities are `periodLength (oddLengths d)`, `slotPrefix (oddLengths d) i` and `d i`. The subtraction $R-2$ is truncated natural-number subtraction; the hypothesis $t<(R-2)P$ forces $R\ge3$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Chunks.lean#L165-L193

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
universe uJ
open scoped BigOperators
open Finset
variable {r : ℕ}

theorem OAI.AsymptoticallyMinimalLittlewood.Packing.interior_center_exists (d : Fin r → ℕ) {R t : ℕ}
    (ht : t<(R-2)*periodLength (oddLengths d)) (i : Fin r) :
    ∃ p s : ℕ, p+1<R ∧ s<periodLength (oddLengths d) ∧
      p*periodLength (oddLengths d)+s+slotPrefix (oddLengths d) i+d i+1 =
        periodLength (oddLengths d)+1+t := by sorry
