-- Prove2me | Theorems.Thm_MusicStreaming_Core_harsanyi_dividends
-- name    : MusicStreaming.Core.harsanyi_dividends
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:30.487276+00:00
-- url     : https://prove2.me/theorems/7665bf21-4bb1-483a-92b7-567e019d801d
-- title:
--   Appendix, p. 22 — Harsanyi (1959): the dividends $\Delta_v(R)$ are the unique weights with $v=\sum_{\emptyset\neq R}\Delta_v(R)u_R$
-- statement:
--   Let $N=\{1,\dots,n\}$ and let $v:2^N\to\mathbb R$ be a TU game, so $v(\emptyset)=0$. For a nonempty coalition $R\subseteq N$ let $u_R$ be the unanimity game, $u_R(S)=1$ if $R\subseteq S$ and $u_R(S)=0$ otherwise, and let $\Delta_v(R)=\sum_{S\subseteq R}(-1)^{|R|-|S|}v(S)$ be the Harsanyi dividend. Then
--
--   1. the dividends are weights for the unanimity decomposition of $v$:
--   $$v(S)=\sum_{\emptyset\neq R\subseteq N}\Delta_v(R)\,u_R(S)\qquad\text{for every } S\subseteq N;$$
--   2. they are the only such weights: if real numbers $w(R)$ satisfy $v(S)=\sum_{\emptyset\neq R\subseteq N}w(R)\,u_R(S)$ for every $S\subseteq N$, then $w(R)=\Delta_v(R)$ for every nonempty $R$.
--
--   This is the classical result of Harsanyi (1959) that the paper cites to define the dividends; it lets the dividends of the streaming game be read off from any unanimity decomposition.
--
--   **Formalization Note** The bare existence of some weights is already proved on the platform (`MonotonicSolutions.StrongMono.exists_unanimity_expansion`, Young 1985, referenced by this mission); this statement adds what is new: that the explicit formula $\Delta_v$ gives weights, and uniqueness. The hypothesis $v(\emptyset)=0$ is part of the paper's definition of a TU game (p. 13) and is necessary, since the right-hand side vanishes at $S=\emptyset$. The unanimity game is the published `MonotonicSolutions.StrongMono.unanimity`.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 22, Appendix, proof of Theorem 2 (citing Harsanyi 1959)

import Mathlib
import Definitions.Def_MonotonicSolutions_StrongMono_Unanimity
import Definitions.Def_MusicStreaming_Core_Harsanyi

namespace MusicStreaming.Core

/-- Harsanyi (1959), cited on p. 22: for every TU game `v` (`v ∅ = 0`), the dividends
`Δ_v(R) = ∑_{S ⊆ R} (-1)^{|R|-|S|} v(S)` are weights with `v = ∑_{∅ ≠ R ⊆ N} Δ_v(R) u_R`, and any
weights `w` with `v = ∑_{∅ ≠ R ⊆ N} w(R) u_R` agree with them on every nonempty `R`. -/
theorem harsanyi_dividends {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : v ∅ = 0) :
    (∀ S : Finset (Fin n), v S = ∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty),
        dividend v R * MonotonicSolutions.StrongMono.unanimity R S) ∧
    ∀ w : Finset (Fin n) → ℝ,
      (∀ S : Finset (Fin n), v S = ∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty),
        w R * MonotonicSolutions.StrongMono.unanimity R S) →
      ∀ R : Finset (Fin n), R.Nonempty → w R = dividend v R := by sorry

end MusicStreaming.Core
