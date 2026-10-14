-- Prove2me | Theorems.Thm_MusicStreaming_Core_harsanyiSet_subset_allocSet
-- name    : MusicStreaming.Core.harsanyiSet_subset_allocSet
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:41.935241+00:00
-- url     : https://prove2.me/theorems/183460b5-62d5-4754-926a-833fdea86c0a
-- title:
--   Appendix, p. 23 — $H(N,v)\subseteq A(N,M,t)$ for the streaming game
-- statement:
--   Let $(N,M,t)$ be a streaming problem with streaming game $v(S)=|\{j\in M:L^j\subseteq S\}|$, Harsanyi set $H(N,v)$ (the allocations $y^p_i=\sum_{R\ni i}\Delta_v(R)p^R_i$ induced by sharing systems $p$) and allocation set $A(N,M,t)$ (sums over users $j\in M$ of nonnegative vectors supported on $L^j$ with total $1$). Then
--   $$H(N,v)\subseteq A(N,M,t).$$
--
--   Every way of splitting the dividends of the streaming game among coalition members is a way of splitting each user's payment among the artists that user played.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 23, Appendix, proof of Theorem 2, second paragraph

import Mathlib
import Definitions.Def_MusicStreaming_Core_Setting
import Definitions.Def_MusicStreaming_Core_Harsanyi

namespace MusicStreaming.Core

/-- Proof of Theorem 2, p. 23: the Harsanyi set of the streaming game lies in the allocation set,
`H(N, v) ⊆ A(N, M, t)`. -/
theorem harsanyiSet_subset_allocSet {n : ℕ} (t : MusicStreaming.Axioms.Problem n) :
    harsanyiSet (game t) ⊆ allocSet t := by sorry

end MusicStreaming.Core
