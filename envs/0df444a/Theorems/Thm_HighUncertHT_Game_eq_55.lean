-- Prove2me | Theorems.Thm_HighUncertHT_Game_eq_55
-- name    : HighUncertHT.Game.eq_55
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:30.285623+00:00
-- url     : https://prove2.me/theorems/77e290d4-8cf6-41b7-b6d3-1605e39cd3ac
-- title:
--   (55) with (59)–(61), pp. 31–32 — V(0) ≤ liminf Cⁿ(β*ⁿ(a*ⁿ), a*ⁿ) for the feedback control a*ⁿ
-- statement:
--   Let $u$ be the classical solution of (HJB), and for each $n\ge1$ and type $\ell$ let $\psi^{\ell n}$ be a measurable selector as in Theorem 2.2 (equivalently, as in (60)). Let $a^{*n}$ be the adversary control that, at every epoch $k\ge1$, chooses
--   $$
--   \pi^{\ell n}_k=\psi^{\ell n}(\mathsf W^n_{k-1})\qquad(61)
--   $$
--   for every type $\ell$, where $\mathsf W^n$ is the Lindley process of §7, and then draws the job sizes according to (7). Such controls exist, and every such sequence satisfies
--   $$
--   u(0)\le\liminf_{n\to\infty}C^n(\beta^{*n}(a^{*n}),a^{*n}) .
--   $$
--
--   Combined with Theorem 1, this gives the lower bound $\liminf_nV^n\ge u(0)$ of the goal theorem.
--
--   **Formalization Note** The page writes $\mathsf V(0)$, equal to $u(0)$ by Proposition 1.1, and $C$ for $C^n$. The control $a^{*n}$ is identified by its feedback map; the statement asserts that a control with this feedback map exists (the measurability of the kernel it induces) and proves the bound for it. The selector condition of (60), a maximum over $\Pi^{\ell n}$, is stated in the equivalent form of Theorem 2.2 (a linear function has the same supremum over $K^{\ell n}$ and over its closed convex hull). Formula (61), not the control (15) of Theorem 2.3, is the one §7 analyses.
-- source:
--   Atar, Castiel, Shadmi, Scheduling in the High Uncertainty Heavy Traffic Regime, arXiv:2204.05733v1, pp. 31–32, display (55), with (59), (60), (61)

import Mathlib
import Definitions.Def_HighUncertHT_Game_Setting
import Definitions.Def_HighUncertHT_Game_System
import Definitions.Def_HighUncertHT_Game_Control
import Definitions.Def_HighUncertHT_Game_Priority
import Definitions.Def_HighUncertHT_Game_HJB
import Definitions.Def_HighUncertHT_Game_Lindley

namespace HighUncertHT.Game

open MeasureTheory Filter Topology
open scoped ENNReal

/-- (55) with (59)–(61), pp. 31–32: let `ψ^{ℓn}` be measurable maximizing selectors as in
Theorem 2.2 / (60), and let `a^{*n}` be the control that chooses `π^{ℓn}_k = ψ^{ℓn}(Wⁿ_{k-1})`
(61), `Wⁿ` the Lindley process of §7. Such controls exist, and every such sequence satisfies
`V(0) ≤ liminf_n Cⁿ(β^{*n}(a^{*n}), a^{*n})`, with `V(0) = u(0)` (Proposition 1.1). -/
theorem eq_55 {L : ℕ} (S : Setting L) (u : ℝ → ℝ) (hu : IsClassicalSolution S u)
    (ψ : ℕ → Fin L → ℝ → ProbabilityMeasure ℝ)
    (hψ : ∀ n : ℕ, 1 ≤ n → ∀ ℓ : Fin L, Measurable (ψ n ℓ) ∧
      (∀ z : ℝ, 0 ≤ z → ψ n ℓ z ∈ S.cls n ℓ) ∧
      ∀ z : ℝ, 0 ≤ z →
        Hbar (d1 u z) (d2 u z) (drift (ψ n ℓ z) (S.μ ℓ) n) (halfVar (ψ n ℓ z)) =
          Hpre S n ℓ (d1 u z) (d2 u z)) :
    (∃ a : (n : ℕ) → AdversaryControl S n, ∀ n : ℕ, 1 ≤ n → ∀ m x ℓ,
        (a n).policy m x ℓ = ψ n ℓ (lindleyHist n m x)) ∧
    ∀ a : (n : ℕ) → AdversaryControl S n,
      (∀ n : ℕ, 1 ≤ n → ∀ m x ℓ, (a n).policy m x ℓ = ψ n ℓ (lindleyHist n m x)) →
        ENNReal.ofReal (u 0) ≤ liminf (fun n => cost S n (betaStar S n) (a n)) atTop := by sorry

end HighUncertHT.Game
