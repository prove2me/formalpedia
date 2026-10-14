-- Prove2me | Theorems.Thm_MusicStreaming_Core_dividend_game
-- name    : MusicStreaming.Core.dividend_game
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:33.369054+00:00
-- url     : https://prove2.me/theorems/bab36df2-0c0d-423f-9543-9d5c4df84ff7
-- title:
--   Appendix, p. 23 — the dividends of the streaming game are $\Delta_v(R)=|\{j\in M:L^j=R\}|\ge0$
-- statement:
--   Let $(N,M,t)$ be a streaming problem with lists $L^j$ and streaming game $v(S)=|\{j\in M:L^j\subseteq S\}|$, and let $\Delta_v(R)=\sum_{S\subseteq R}(-1)^{|R|-|S|}v(S)$ be its Harsanyi dividends. For every nonempty coalition $R\subseteq N$,
--   $$\Delta_v(R)=\bigl|\{j\in M:L^j=R\}\bigr|\ \ge\ 0.$$
--
--   So the dividend of a coalition is the number of users whose list is exactly that coalition; in particular all dividends are nonnegative, which is the hypothesis of Vasil'ev's theorem.
--
--   **Formalization Note** The two conclusions (the value and its nonnegativity) are stated as a conjunction, as on the page.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 23, Appendix, proof of Theorem 2, first sentence

import Mathlib
import Definitions.Def_MusicStreaming_Core_Setting
import Definitions.Def_MusicStreaming_Core_Harsanyi

namespace MusicStreaming.Core

/-- Proof of Theorem 2, p. 23: for every nonempty coalition `R`, the Harsanyi dividend of the
streaming game is the number of users whose list is exactly `R`, hence nonnegative:
`Δ_v(R) = |{j ∈ M : L^j = R}| ≥ 0`. -/
theorem dividend_game {n : ℕ} (t : MusicStreaming.Axioms.Problem n) (R : Finset (Fin n)) (hR : R.Nonempty) :
    dividend (game t) R = ((t.support.filter (fun j => MusicStreaming.Axioms.listened t j = R)).card : ℝ) ∧
      0 ≤ dividend (game t) R := by sorry

end MusicStreaming.Core
