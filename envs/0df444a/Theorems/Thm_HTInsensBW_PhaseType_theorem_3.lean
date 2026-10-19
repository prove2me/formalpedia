-- Prove2me | Theorems.Thm_HTInsensBW_PhaseType_theorem_3
-- name    : HTInsensBW.PhaseType.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:15:27.915989+00:00
-- url     : https://prove2.me/theorems/14f410d0-2841-4ea9-a678-51e39efc5b71
-- title:
--   Theorem 3, p. 25 — state-space collapse: E[‖N̄_⊥‖^m] = O((1/√ε)^m)
-- statement:
--   Under the standing assumptions of the paper (see Lemma 7), let $\overline{\mathbf N}^{(\epsilon)}$ be distributed as the stationary distribution of the flow-count process of the $\epsilon$-th system and $\|\overline{\mathbf N}^{(\epsilon)}_\perp\|$ its distance to the cone $\mathcal K$ of (61) under the constructed inner product. Then for every nonnegative integer $m$, as $\epsilon\to0^+$,
--   $$\mathbb E\Big[\big\|\overline{\mathbf N}^{(\epsilon)}_\perp\big\|^m\Big]=O\Big(\Big(\frac1{\sqrt\epsilon}\Big)^m\Big):$$
--   there are $C_m>0$ and $\epsilon_1>0$ such that the $m$-th moment is finite and at most $C_m(1/\sqrt\epsilon)^m$ for all $0<\epsilon<\epsilon_1$.
--
--   Since $\mathbb E[\|\overline{\mathbf N}^{(\epsilon)}\|]$ is of order $1/\epsilon$, the stationary flow-count vector concentrates around the $L_s$-dimensional cone $\mathcal K$: this is the state-space collapse that reduces Theorem 4 to the cone.
--
--   **Formalization Note** "The stationary distribution" is read as every stationary distribution (it exists by Lemma 7 and is unique by irreducibility).
-- source:
--   Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, p. 25, Theorem 3

import Mathlib
import Definitions.Def_HTInsensBW_PhaseType_Model
import Definitions.Def_HTInsensBW_PhaseType_InnerProduct

namespace HTInsensBW.PhaseType

open Matrix MeasureTheory

/-- **Theorem 3, p. 25 — state-space collapse.** (Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, p. 25, Theorem 3.)
For every `m ∈ ℕ` there are `C_m > 0` and `ε_1 > 0` such that for all `0 < ε < ε_1` and every
stationary distribution `π` of the `ε`-th system, `E_π[‖N̄_⊥‖^m]` is finite and at most
`C_m (1/√ε)^m`; i.e. `E[‖N̄^(ε)_⊥‖^m] = O((1/√ε)^m)` as `ε → 0+`.

**Formalization Note** The standing hypotheses of §2 and §6 are explicit: `H` has 0/1 entries and full row rank
(p. 5); every route uses at least one link and every capacity is positive (implicit on p. 5 and in
(31): without them the allocation problem (2)–(4) has no optimum); `κ_r > 0` and `λ^(0)_r > 0`
(pp. 5, 7); `λ^(0)` is on the boundary of the capacity region, encoded as (7)–(8):
`Σ_{r : ℓ ∈ r} ρ^(0)_r ≤ C_ℓ` for all links with at least one link critical (`L_s ≠ ∅`); and `x` is
the weighted proportionally fair allocation (2)–(4), as a function of the route totals. The class
`D` (p. 22) is carried by the fields of `PhaseTypeD`.
`O(·)` as `ε → 0+` is the existence of a constant and a threshold, both chosen before `ε`.
"the stationary distribution" is read as every stationary distribution (existence and uniqueness
hold by Lemma 7 and irreducibility). -/
theorem theorem_3 {L R : ℕ} (N : BWNetwork L R)
    (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1) (hrank : N.H.rank = L)
    (hroute : ∀ r, ∃ ℓ, N.H ℓ r = 1) (hC : ∀ ℓ, 0 < N.C ℓ)
    (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r)
    (hload : ∀ ℓ, ∑ r, N.H ℓ r * routeLoad0 N r ≤ N.C ℓ) (hLs : (critical N).Nonempty)
    (x : (Fin R → ℕ) → Fin R → ℝ) (hx : ∀ m, IsWPFAllocation N m (x m)) :
    ∀ m : ℕ, ∃ Cm : ℝ, 0 < Cm ∧ ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → ε < ε₁ →
        ∀ π : State N → ℝ, IsStationary (rates N x ε) π →
          Summable (fun n => π n * perpNorm N (toReal N n) ^ m) ∧
          ∑' n, π n * perpNorm N (toReal N n) ^ m ≤ Cm * (1 / Real.sqrt ε) ^ m := by sorry

end HTInsensBW.PhaseType
