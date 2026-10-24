-- Prove2me | Theorems.Thm_HiringLP_Parallel_lemma_9
-- name    : HiringLP.Parallel.lemma_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:07.055477+00:00
-- url     : https://prove2.me/theorems/f31f1ee5-f017-416c-aecb-570ad4cd2d46
-- title:
--   Lemma 9, p. 24 — with identical positions, LP_par(I) = LP_seq(I′) for the sequential instance with kT offers
-- statement:
--   Let $I=(k,T,n,p,v)$ be a valid Parallel Offering instance whose positions are identical: $v_{ij}=w_i$ and $p_{ij}=q_i$ for all $i\in[n]$, $j\in[k]$. Let $I'$ be the Sequential Offering instance with the same candidates (acceptance probabilities $q_i$, values $w_i$), the same $k$ positions and a budget of $kT$ sequential offers. Then
--   $$\mathrm{LP}_{\mathrm{par}}(I)=\mathrm{LP}_{\mathrm{seq}}(I').$$
--
--   Combined with Theorem 2 this bounds the cost of sending offers in $T$ parallel batches instead of $kT$ single sequential offers by a factor $1-1/e$ (Corollary 3 of the paper, not posed here).
--
--   **Formalization Note** Both sides are the suprema of the respective LP objectives over their feasible sets.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 24, §5.4, Lemma 9 (LPseq on p. 21; proof App. C.6, p. ec12)

import Mathlib
import Definitions.Def_HiringLP_Parallel_Model

namespace HiringLP.Parallel

/-- Lemma 9 (p. 24): if all positions are identical (`v_ij = w_i`, `p_ij = q_i`), then
`LP_par(I) = LP_seq(I′)`, where `I′` has the same candidates, the same `k` positions and a budget
of `kT` sequential offers. -/
theorem lemma_9 {n k : ℕ} (I : Instance n k) (hI : I.Valid) (q w : Fin n → ℝ)
    (hp : ∀ i j, I.p i j = q i) (hv : ∀ i j, I.v i j = w i) :
    LPpar I = LPseq (seqOfIdentical I q w) := by sorry

end HiringLP.Parallel
