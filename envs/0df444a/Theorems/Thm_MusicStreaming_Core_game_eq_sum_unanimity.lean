-- Prove2me | Theorems.Thm_MusicStreaming_Core_game_eq_sum_unanimity
-- name    : MusicStreaming.Core.game_eq_sum_unanimity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:38.537511+00:00
-- url     : https://prove2.me/theorems/eb54ce2f-c2f5-4c6c-aa2a-d66866e21291
-- title:
--   Appendix, p. 22 — the streaming game is $v=\sum_{\emptyset\neq R}|\{j\in M:L^j=R\}|\,u_R$
-- statement:
--   Let $(N,M,t)$ be a streaming problem with lists $L^j=\{i\in N:t_{ij}>0\}$ and streaming game $v(S)=|\{j\in M:L^j\subseteq S\}|$. For a nonempty coalition $R\subseteq N$ let $u_R$ be the unanimity game ($u_R(S)=1$ if $R\subseteq S$, else $0$). Then for every coalition $S\subseteq N$,
--   $$v(S)=\sum_{\emptyset\neq R\subseteq N}\bigl|\{j\in M:L^j=R\}\bigr|\,u_R(S).$$
--
--   The streaming game is thus a nonnegative integer combination of unanimity games, one unit for each user, placed on that user's list.
--
--   **Formalization Note** The identity holds because every user in $M$ has a nonempty list (built into the encoding of problems). The unanimity game is the published `MonotonicSolutions.StrongMono.unanimity`.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 22, Appendix, proof of Theorem 2, last display

import Mathlib
import Definitions.Def_MonotonicSolutions_StrongMono_Unanimity
import Definitions.Def_MusicStreaming_Core_Setting

namespace MusicStreaming.Core

/-- Proof of Theorem 2, p. 22: the streaming game is the sum of unanimity games
`v = ∑_{∅ ≠ R ⊆ N} |{j ∈ M : L^j = R}| u_R`. -/
theorem game_eq_sum_unanimity {n : ℕ} (t : MusicStreaming.Axioms.Problem n) (S : Finset (Fin n)) :
    game t S = ∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty),
      ((t.support.filter (fun j => MusicStreaming.Axioms.listened t j = R)).card : ℝ) *
        MonotonicSolutions.StrongMono.unanimity R S := by sorry

end MusicStreaming.Core
