-- Prove2me | Theorems.Thm_MusicStreaming_Core_allocSet_subset_harsanyiSet
-- name    : MusicStreaming.Core.allocSet_subset_harsanyiSet
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:29.525804+00:00
-- url     : https://prove2.me/theorems/febb60cc-1834-4f32-964e-3419ae757bb6
-- title:
--   Appendix, p. 23 — $A(N,M,t)\subseteq H(N,v)$ for the streaming game
-- statement:
--   Let $(N,M,t)$ be a streaming problem with streaming game $v(S)=|\{j\in M:L^j\subseteq S\}|$, allocation set $A(N,M,t)$ and Harsanyi set $H(N,v)$. Then
--   $$A(N,M,t)\subseteq H(N,v).$$
--
--   Every split of the users' payments among the artists they played arises from a sharing system of the dividends of the streaming game.
--
--   **Formalization Note** The page's construction of the sharing system assigns $p^R_i=1/|N|$ to coalitions $R$ that are no user's list, which violates $p^R_i=0$ outside $R$; any probability vector on $R$ serves there, since the dividend of such $R$ is $0$. This concerns only the proof; the statement is the page's.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 23, Appendix, proof of Theorem 2, third paragraph

import Mathlib
import Definitions.Def_MusicStreaming_Core_Setting
import Definitions.Def_MusicStreaming_Core_Harsanyi

namespace MusicStreaming.Core

/-- Proof of Theorem 2, p. 23: the allocation set lies in the Harsanyi set of the streaming game,
`A(N, M, t) ⊆ H(N, v)`. -/
theorem allocSet_subset_harsanyiSet {n : ℕ} (t : MusicStreaming.Axioms.Problem n) :
    allocSet t ⊆ harsanyiSet (game t) := by sorry

end MusicStreaming.Core
