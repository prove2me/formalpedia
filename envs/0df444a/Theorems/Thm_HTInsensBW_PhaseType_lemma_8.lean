-- Prove2me | Theorems.Thm_HTInsensBW_PhaseType_lemma_8
-- name    : HTInsensBW.PhaseType.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:15:19.684743+00:00
-- url     : https://prove2.me/theorems/fd572fd6-b04e-47a5-b50f-394e792de360
-- title:
--   Lemma 8, pp. 27–28 — drift bounds (68)–(71) for the distance ‖n_⊥‖ to the cone
-- statement:
--   Under the standing assumptions of the paper (see Lemma 7), with $\|\mathbf n_\perp\|$ the distance from $\mathbf n$ to the cone $\mathcal K$ of (61) in the norm (65), there are positive constants $\epsilon_{\max},A_1,A_2$ such that for all constants $\xi_1>0$, $\xi_2>0$ with $\xi_2-\xi_1=2$, every $0<\epsilon<1$ with $\epsilon\le\epsilon_{\max}$ and every state $\mathbf n$:
--   $$\Delta^{(\epsilon)}\|\mathbf n_\perp\|\le-\sqrt\epsilon\quad\text{when}\quad\|\mathbf n_\perp\|\ge\frac{A_1}{\xi_1\sqrt\epsilon},\quad\frac{\|\mathbf n_\perp\|}{\sum_r\kappa_rn_r}\ge\frac{\xi_2\sqrt\epsilon}{A_2},$$
--   and
--   $$\Delta^{(\epsilon)}\|\mathbf n_\perp\|\le(\xi_1+1)\sqrt\epsilon\quad\text{when}\quad\|\mathbf n_\perp\|\ge\frac{A_1}{\xi_1\sqrt\epsilon}.$$
--
--   These drift bounds, fed into Lemma 10 together with the tail of Lemma 7, give the state-space collapse of Theorem 3.
--
--   **Formalization Note** The page lists $\xi_1,\xi_2$ among "positive constants"; its proof (p. 28) takes "any constants $\xi_1>0,\xi_2>0$ such that $\xi_2-\xi_1=2$" with $\epsilon_{\max},A_1,A_2$ independent of them, and the proof of Theorem 3 uses that freedom, so $\xi_1,\xi_2$ are universally quantified after the other constants.
-- source:
--   Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, pp. 27–28, Lemma 8, (68)–(71)

import Mathlib
import Definitions.Def_HTInsensBW_PhaseType_Model
import Definitions.Def_HTInsensBW_PhaseType_InnerProduct

namespace HTInsensBW.PhaseType

open Matrix MeasureTheory

/-- **Lemma 8, pp. 27–28 — drift bounds for `‖n_⊥‖`, (68)–(71).**
(Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, pp. 27–28, Lemma 8, (68)–(71).)
There are positive constants `ε_max, A_1, A_2` such that for all positive `ξ_1, ξ_2` with
`ξ_2 - ξ_1 = 2`, every `0 < ε < 1` with `ε ≤ ε_max` and every state `n`:
`Δ^(ε)‖n_⊥‖ ≤ -√ε` when `‖n_⊥‖ ≥ A_1/(ξ_1 √ε)` and `‖n_⊥‖ / Σ_r κ_r n_r ≥ ξ_2 √ε / A_2`; and
`Δ^(ε)‖n_⊥‖ ≤ (ξ_1 + 1) √ε` when `‖n_⊥‖ ≥ A_1/(ξ_1 √ε)`.

**Formalization Note** The standing hypotheses of §2 and §6 are explicit: `H` has 0/1 entries and full row rank
(p. 5); every route uses at least one link and every capacity is positive (implicit on p. 5 and in
(31): without them the allocation problem (2)–(4) has no optimum); `κ_r > 0` and `λ^(0)_r > 0`
(pp. 5, 7); `λ^(0)` is on the boundary of the capacity region, encoded as (7)–(8):
`Σ_{r : ℓ ∈ r} ρ^(0)_r ≤ C_ℓ` for all links with at least one link critical (`L_s ≠ ∅`); and `x` is
the weighted proportionally fair allocation (2)–(4), as a function of the route totals. The class
`D` (p. 22) is carried by the fields of `PhaseTypeD`.
`‖n_⊥‖` is the distance from `n` to the cone `K` (61) in the norm (65). The page lists `ξ_1, ξ_2`
among "positive constants"; its proof (p. 28) takes "any constants ξ_1 > 0, ξ_2 > 0 such that
ξ_2 - ξ_1 = 2" with `ε_max, A_1, A_2` independent of them, and Theorem 3 uses that freedom, so
`ξ_1, ξ_2` are universally quantified after the other constants. -/
theorem lemma_8 {L R : ℕ} (N : BWNetwork L R)
    (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1) (hrank : N.H.rank = L)
    (hroute : ∀ r, ∃ ℓ, N.H ℓ r = 1) (hC : ∀ ℓ, 0 < N.C ℓ)
    (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r)
    (hload : ∀ ℓ, ∑ r, N.H ℓ r * routeLoad0 N r ≤ N.C ℓ) (hLs : (critical N).Nonempty)
    (x : (Fin R → ℕ) → Fin R → ℝ) (hx : ∀ m, IsWPFAllocation N m (x m)) :
    ∃ εmax A1 A2 : ℝ, 0 < εmax ∧ 0 < A1 ∧ 0 < A2 ∧
      ∀ ξ1 ξ2 : ℝ, 0 < ξ1 → 0 < ξ2 → ξ2 - ξ1 = 2 →
      ∀ ε : ℝ, 0 < ε → ε < 1 → ε ≤ εmax → ∀ n : State N,
        (A1 / (ξ1 * Real.sqrt ε) ≤ perpNorm N (toReal N n) →
          ξ2 * Real.sqrt ε / A2 ≤ perpNorm N (toReal N n) / wsum N n →
          drift (rates N x ε) (fun n' => perpNorm N (toReal N n')) n ≤ -Real.sqrt ε) ∧
        (A1 / (ξ1 * Real.sqrt ε) ≤ perpNorm N (toReal N n) →
          drift (rates N x ε) (fun n' => perpNorm N (toReal N n')) n ≤
            (ξ1 + 1) * Real.sqrt ε) := by sorry

end HTInsensBW.PhaseType
