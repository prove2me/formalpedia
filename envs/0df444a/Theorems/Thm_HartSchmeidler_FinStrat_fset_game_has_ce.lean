-- Prove2me | Theorems.Thm_HartSchmeidler_FinStrat_fset_game_has_ce
-- name    : HartSchmeidler.FinStrat.fset_game_has_ce
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:08:58.729722+00:00
-- url     : https://prove2.me/theorems/2c969638-bba2-45a6-9e6d-8b5c177909d3
-- title:
--   Proof of Theorem 2 — every f-set game has a correlated equilibrium
-- statement:
--   Let $N$ be a nonempty set of players, each with a nonempty finite strategy set $S^i$, and let each real payoff $h^i$ be bounded on the full profile space $S$. For every f-set $T=\prod_iT^i$, the restricted game $\Gamma_T$ has a finite weighted correlated equilibrium: there are finitely many profiles $F\subseteq T$ and nonnegative weights $w_s$ summing to one such that
--
--   $$\sum_{\substack{s\in F\\s^i=r^i}}w_s\bigl[h^i(s)-h^i(s^{-i},t^i)\bigr]\ge0\qquad(i\in N,\ r^i,t^i\in T^i).$$
--
--   This supplies the approximating equilibria $q_T$ in the proof of Theorem 2. No continuity is required for this finite-game step.
--
--   **Formalization Note.** An f-set has nonempty $T^i$ and only finitely many nonsingleton coordinates. The boundedness hypothesis records §3's standing game convention; finite restrictions themselves require no continuity. Profiles in $F$ are supported on $T$, and zero-weight profiles may be included in $F$ without changing the represented distribution.
-- source:
--   Hart and Schmeidler, Existence of Correlated Equilibria, Math. Oper. Res. 14 (1989), p. 22, proof of Theorem 2 (f-set game and q_T)

import Definitions.Def_HartSchmeidler_FinStrat_Game

namespace HartSchmeidler.FinStrat

open MeasureTheory

/-- Proof of Theorem 2, pp. 22–23: every f-set game Γ_T has a finite-support
correlated equilibrium, whether or not the payoff functions are continuous. -/
theorem fset_game_has_ce {ι : Type*} [Nonempty ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    [∀ i, Nonempty (S i)]
    (h : ι → (∀ i, S i) → ℝ)
    (hbounded : ∀ i, ∃ C : ℝ, ∀ s, |h i s| ≤ C)
    (T : ∀ i, Finset (S i))
    (hT : IsFSet T) :
    ∃ (F : Finset (∀ i, S i)) (w : (∀ i, S i) → ℝ), IsFSetCE h T F w := by sorry

end HartSchmeidler.FinStrat
