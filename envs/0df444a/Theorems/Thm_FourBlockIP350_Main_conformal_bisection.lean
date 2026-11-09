-- Prove2me | Theorems.Thm_FourBlockIP350_Main_conformal_bisection
-- name    : FourBlockIP350.Main.conformal_bisection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:24.470677+00:00
-- url     : https://prove2.me/theorems/990c69cd-f19a-464f-8ea6-08a891ab2082
-- title:
--   Corollary 2.7 — Conformal bisection
-- statement:
--   Let $Q$ be a generalized n-fold matrix with block and entry bounds $k,\bar\Delta\ge1$, and let $N>0$ be a uniform IDP period from Proposition 2.6. For integral $\delta,w$ satisfying $Q\delta=2Nw$, there exist integral vectors such that
--   $$\delta=\delta'+\delta'',\quad\delta',\delta''\sqsubseteq\delta,\quad Q\delta'=Q\delta''=Nw.$$
--   This divides an integral displacement while preserving both the equalities and coordinatewise conformality.
--
--   Differences from the source:
--   - encoding: N is the positive integer of Proposition 2.6 → N > 0 and UniformDilation k Δbar N; reason: this spells out the upstream property uniformly over the whole matrix class, including column sign changes
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 6, Corollary 2.7

import Mathlib
import Definitions.Def_FourBlockIP350_Main_Decomposition

namespace FourBlockIP350.Main

open scoped BigOperators

theorem conformal_bisection {k n Δ N : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hΔ : 0 < Δ) (hN : 0 < N) (hdil : UniformDilation k Δ N)
    (Q : NFold k n) (hQ : Q.Bounded Δ)
    (δ : LocalCol k n → ℤ) (w : BlockRow k n → ℤ)
    (heq : Q.matrix.mulVec δ = (2 * (N : ℤ)) • w) :
    ∃ δ' δ'' : LocalCol k n → ℤ,
      δ = δ' + δ'' ∧ Conformal δ' δ ∧ Conformal δ'' δ ∧
      Q.matrix.mulVec δ' = (N : ℤ) • w ∧ Q.matrix.mulVec δ'' = (N : ℤ) • w := by sorry

end FourBlockIP350.Main
