-- Prove2me | Theorems.Thm_HighUncertHT_Game_theorem_2_2
-- name    : HighUncertHT.Game.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:40.964084+00:00
-- url     : https://prove2.me/theorems/b5b21fb0-e50d-4e52-9cfc-489fb5c8dc23
-- title:
--   Theorem 2.2, p. 10 — a measurable selector ψ^{ℓn} : ℝ₊ → Π^{ℓn} attaining H^{ℓn}(u′, u″)
-- statement:
--   Let $u$ be the classical solution of (HJB). For each $n\ge1$ and each type $\ell$ there exists a measurable function $\psi^{\ell n}:\mathbb R_+\to\Pi^{\ell n}$ such that
--   $$
--   \bar H\big(u'(z),u''(z),b^{\psi^{\ell n}(z),\ell n},q^{\psi^{\ell n}(z)}\big)=H^{\ell n}(u'(z),u''(z)),\qquad z\in\mathbb R_+ .
--   $$
--
--   The selector is a member of the uncertainty class itself that attains the prelimit Hamiltonian; it is the building block of the adversary's asymptotically optimal feedback control.
--
--   **Formalization Note** $\psi^{\ell n}$ is typed $\mathbb R\to$ `ProbabilityMeasure ℝ`; membership and the identity are required for $z\ge0$ only (any measurable map on $\mathbb R_+$ extends measurably).
-- source:
--   Atar, Castiel, Shadmi, Scheduling in the High Uncertainty Heavy Traffic Regime, arXiv:2204.05733v1, p. 10, Theorem 2.2

import Mathlib
import Definitions.Def_HighUncertHT_Game_Setting
import Definitions.Def_HighUncertHT_Game_HJB

namespace HighUncertHT.Game

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Theorem 2.2, p. 10: for the classical solution `u` of (HJB), every `n ≥ 1` and every type
`ℓ` there is a measurable `ψ^{ℓn} : ℝ₊ → Π^{ℓn}` with
`H̄(u′(z), u″(z), b^{ψ^{ℓn}(z),ℓn}, q^{ψ^{ℓn}(z)}) = H^{ℓn}(u′(z), u″(z))` for all `z ≥ 0`. -/
theorem theorem_2_2 {L : ℕ} (S : Setting L) (u : ℝ → ℝ) (hu : IsClassicalSolution S u)
    (n : ℕ) (hn : 1 ≤ n) (ℓ : Fin L) :
    ∃ ψ : ℝ → ProbabilityMeasure ℝ, Measurable ψ ∧ (∀ z : ℝ, 0 ≤ z → ψ z ∈ S.cls n ℓ) ∧
      ∀ z : ℝ, 0 ≤ z →
        Hbar (d1 u z) (d2 u z) (drift (ψ z) (S.μ ℓ) n) (halfVar (ψ z)) =
          Hpre S n ℓ (d1 u z) (d2 u z) := by sorry

end HighUncertHT.Game
