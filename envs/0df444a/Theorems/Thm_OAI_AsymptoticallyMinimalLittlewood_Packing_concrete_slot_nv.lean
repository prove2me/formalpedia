-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_concrete_slot_nv
-- name    : OAI.AsymptoticallyMinimalLittlewood.Packing.concrete_slot_nv
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:44:44.776469+00:00
-- url     : https://prove2.me/theorems/622ac903-30cc-4a32-ab73-590d919643cb
-- title:
--   Every slot choice hits exactly $rK(R-1)$ slot vertices
-- statement:
--   Let $r\ge1$ and $d=(d_0,\dots,d_{r-1})\in\mathbb{N}^r$. Put $L_i=2d_i+1$, $L=\sum_{i}L_i$ and $P_i=\sum_{j<i}L_j$. Let $R\ge1$ be an integer and $q$ a prime, write $\mathbb{F}_q=\mathbb{Z}/q\mathbb{Z}$, and put
--   $$K=\Big\lfloor\frac{q-1}{2RL}\Big\rfloor .$$
--   A *slot choice* is a family $\omega=(\sigma_k,\epsilon_k)_{0\le k<K}$ of shifts $\sigma_k\in\{0,\dots,L-1\}$ and signs $\epsilon_k\in\{+1,-1\}$. Row $i$ is *hit* at $u\in\mathbb{F}_q$ under $\omega$ if $u\equiv\epsilon_k\big(kRL+pL+\sigma_k+P_i+d_i+1\big)\pmod q$ for some $0\le k<K$ and $0\le p<R-1$, and the set of *slot vertices* of $\omega$ is
--   $$U_\omega=\big\{(i,u)\in\{0,\dots,r-1\}\times\mathbb{F}_q:\ \text{row } i \text{ is hit at } u \text{ under } \omega\big\}.$$
--   Then for every slot choice $\omega$
--   $$|U_\omega|=q\cdot N_q,\qquad N_q=r\,(R-1)\,\frac{K}{q};$$
--   equivalently, $|U_\omega|=rK(R-1)$.
--
--   The number of vertices of the slot hypergraph is therefore the same for all slot choices, as required in the random matching step (with $n=qN_q$), and the normalized count $N_q$ tends to $r(1-1/R)/(2L)$ as $q\to\infty$.
--
--   **Formalization Note** $N_q$ is `packingNV r L R q` (with $R-1$ a real difference), $K$ is `chunkCount (2*R*L) q`, $U_\omega$ is `slotVertices` of the hit relation `slotHit d R K q`, and slot choices are `SlotChoices d K`. An index $i_0$ of type `Fin r` is an argument only to guarantee $r\ge1$, hence $L>0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/SlotParameters.lean#L252-L268

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
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
universe uV
open scoped BigOperators
open Finset Nibble Filter Topology
attribute [local instance] Classical.propDecidable

theorem OAI.AsymptoticallyMinimalLittlewood.Packing.concrete_slot_nv {r q R : ℕ} [Fact q.Prime]
    (d : Fin r → ℕ) (i₀ : Fin r) (hR : 1≤R)
    (ω : SlotChoices d (chunkCount (2*R*periodLength (oddLengths d)) q)) :
    ((slotVertices (fun i t ↦ slotHit d R
      (chunkCount (2*R*periodLength (oddLengths d)) q) q i ω t)).card : ℝ)=
      (q : ℝ)*packingNV r (periodLength (oddLengths d)) R q := by sorry
