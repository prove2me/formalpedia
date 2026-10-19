-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_siteCenter_chunk
-- name    : OAI.AsymptoticallyMinimalLittlewood.Packing.siteCenter_chunk
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:28:44.596283+00:00
-- url     : https://prove2.me/theorems/379096db-fee3-4598-9f52-6e98eb583fc7
-- title:
--   Integer division by the chunk length recovers the chunk of a slot center
-- statement:
--   Let $r\ge1$ and $d:\{0,\dots,r-1\}\to\mathbb N$. The odd slot lengths are $L_i=2d_i+1$, the period length is $P=\sum_{i<r}L_i$, and the prefix of slot $i$ is $\pi_i=\sum_{j<i}L_j$, so that slot $i$ occupies the positions $\pi_i+1,\dots,\pi_i+L_i$ of a period and has central position $\pi_i+d_i+1$. For natural numbers $R$ (periods per chunk), $s$ (shift), $k$ (chunk index), $p$ (period index) and a slot $i$, the site center
--   $$
--   c(s,k,p,i)=kRP+pP+s+\pi_i+d_i+1
--   $$
--   is the central site of slot $i$ in period $p$ of chunk $k$, after shifting the periodic pattern by $s$.
--
--   **Theorem.** If $s<P$ and $p+1<R$, then
--
--   $$
--   \Big\lfloor\frac{c(s,k,p,i)}{RP}\Big\rfloor=k .
--   $$
--
--   So as long as the shift is less than one period and the period index is at most $R-2$, every site center of chunk $k$ lies in the integer interval $[kRP,(k+1)RP)$ of that chunk, and the chunk index is recovered from the center by integer division. This is used to show that signed site centers belonging to different chunks never collide and to identify the chunk a residue comes from.
--
--   **Formalization Note** The site center is `siteCenter d R shift chunk period i`, defined through `slotLeft`, `slotPrefix`, `periodLength` and `oddLengths d i = 2 * d i + 1`; the division is natural-number division.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Chunks.lean#L150-L163

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

theorem OAI.AsymptoticallyMinimalLittlewood.Packing.siteCenter_chunk (d : Fin r → ℕ) {R shift chunk period : ℕ}
    (hs : shift<periodLength (oddLengths d)) (hp : period+1<R) (i : Fin r) :
    siteCenter d R shift chunk period i / (R*periodLength (oddLengths d)) = chunk := by sorry
