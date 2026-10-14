-- Prove2me | Theorems.Thm_MusicStreaming_Core_vasilev_core_eq_harsanyiSet
-- name    : MusicStreaming.Core.vasilev_core_eq_harsanyiSet
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:28.608586+00:00
-- url     : https://prove2.me/theorems/6997b1da-cf20-4544-b8cd-7ab53ff020cf
-- title:
--   Appendix, p. 22 — Vasil'ev (1981): nonnegative dividends imply $C(N,v)=H(N,v)$
-- statement:
--   Let $N=\{1,\dots,n\}$ and let $v:2^N\to\mathbb R$ be a TU game ($v(\emptyset)=0$). Its **core** is
--   $$C(N,v)=\Bigl\{x\in\mathbb R^N:\ \sum_{i\in N}x_i=v(N),\ \sum_{i\in S}x_i\ge v(S)\ \text{for every } S\subseteq N\Bigr\},$$
--   and its Harsanyi set $H(N,v)$ is the set of allocations $y^p_i=\sum_{R\ni i}\Delta_v(R)p^R_i$ obtained from sharing systems $p$, where $\Delta_v(R)$ are the Harsanyi dividends. If every dividend is nonnegative, $\Delta_v(R)\ge0$ for every nonempty $R\subseteq N$, then
--   $$C(N,v)=H(N,v).$$
--
--   This is the classical result of Vasil'ev (1981) that the paper cites; applied to the streaming game, whose dividends are user counts, it reduces Theorem 2 to the identity $H(N,v)=A(N,M,t)$.
--
--   **Formalization Note** The core is the published `Supermodularity.Cooperative.Core` with coalition `Finset.univ`. The statement is for every TU game with nonnegative dividends, as cited on the page, not only for the streaming game.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 22, Appendix, proof of Theorem 2 (citing Vasil'ev 1981)

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MusicStreaming_Core_Harsanyi

namespace MusicStreaming.Core

/-- Vasil'ev (1981), cited on p. 22: if every dividend of the TU game `v` (`v ∅ = 0`) is
nonnegative, its core equals its Harsanyi set, `C(N, v) = H(N, v)`. -/
theorem vasilev_core_eq_harsanyiSet {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : v ∅ = 0)
    (hdiv : ∀ R : Finset (Fin n), R.Nonempty → 0 ≤ dividend v R) :
    Supermodularity.Cooperative.Core Finset.univ v = harsanyiSet v := by sorry

end MusicStreaming.Core
