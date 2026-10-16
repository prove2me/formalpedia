-- Prove2me | Theorems.Thm_MusicStreaming_Core_theorem_2
-- name    : MusicStreaming.Core.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:41.000981+00:00
-- url     : https://prove2.me/theorems/fcf343b6-cee8-42a1-a893-7d81326f268a
-- title:
--   Theorem 2, p. 14 — the core of the streaming game is $C(N,v)=A(N,M,t)$
-- statement:
--   Let $N=\{1,\dots,n\}$ be a set of artists and $(N,M,t)$ a streaming problem: $t_{ij}\in\mathbb N$ is the number of times user $j\in M$ played artist $i$, and every user played some artist. Let $L^j=\{i\in N:t_{ij}>0\}$ be the list of user $j$, and let
--   $$v(S)=\bigl|\{j\in M:L^j\subseteq S\}\bigr|\qquad(S\subseteq N)$$
--   be the streaming game, whose core is $C(N,v)=\{x\in\mathbb R^N:\sum_{i\in N}x_i=v(N),\ \sum_{i\in S}x_i\ge v(S)\text{ for every }S\subseteq N\}$. Let $A(N,M,t)$ be the set of vectors $x=\sum_{j\in M}x^j$ where each $x^j\in\mathbb R^N$ is nonnegative, vanishes outside $L^j$ and sums to $1$. Then
--   $$C(N,v)=A(N,M,t).$$
--
--   In words: an allocation of the platform's revenue $m=|M|$ (each user paying $1$) is in the core exactly when it splits each user's payment, in any way, among the artists that user played. In particular the user-centric rewards always lie in the core, which is the basis of the paper's core-selection characterization of the user-centric index (Theorem 3).
--
--   **Formalization Note** A problem is a finitely supported map `t : ℕ →₀ (Fin n → ℕ)` whose support is the user set $M$, so every user in $M$ has a nonempty list (the paper's standing assumption) and $v(\emptyset)=0$. Artists are `Fin n`. The core is the published `Supermodularity.Cooperative.Core Finset.univ`. The statement is a set equality for every problem, including the empty one (where both sides are $\{0\}$); no hypothesis is added.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 14, Theorem 2 (proof pp. 22–23)

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MusicStreaming_Core_Setting

namespace MusicStreaming.Core

/-- **Theorem 2** (p. 14). For every streaming problem `t`, the core `C(N, v)` of the streaming
game `v(S) = |{j ∈ M : L^j ⊆ S}|` equals the set `A(N, M, t)` of allocations that split each
user's payment of `1` among the artists that user played. -/
theorem theorem_2 {n : ℕ} (t : MusicStreaming.Axioms.Problem n) :
    Supermodularity.Cooperative.Core Finset.univ (game t) = allocSet t := by sorry

end MusicStreaming.Core
