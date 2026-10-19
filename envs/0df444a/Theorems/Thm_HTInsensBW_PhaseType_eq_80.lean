-- Prove2me | Theorems.Thm_HTInsensBW_PhaseType_eq_80
-- name    : HTInsensBW.PhaseType.eq_80
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:15:36.176976+00:00
-- url     : https://prove2.me/theorems/4f33b22a-455d-4f0c-b35b-2f9917d0f87c
-- title:
--   (80), p. 30 — the steady-state drift identity for ‖n^s_∥‖²
-- statement:
--   Under the standing assumptions of the paper (see Lemma 7), let $0<\epsilon<1$, let $\overline{\mathbf N}$ be distributed as a stationary distribution of the $\epsilon$-th system, let $\mathbf n^s_\parallel$ denote the $M$-orthogonal projection of $\mathbf n$ onto the span of $\{\mathbf b^{(\ell)}:\ell\in\mathcal L_s\}$, and let $B_1$ be the term defined on p. 30. Then the three expectations below are finite and
--   $$\epsilon\,\mathbb E\big[\langle\overline{\mathbf N}^s_\parallel,(-S^T)\boldsymbol\rho^{(0)}\rangle\big]=\mathbb E\big[\langle\overline{\mathbf N}^s_\parallel,(-S^T)(\boldsymbol\rho^{(0)}-\overline{\mathbf N}\mathbf x)\rangle\big]+\tfrac12\,\mathbb E\big[B_1(\overline{\mathbf N})\big].$$
--
--   It expresses $\mathbb E[\Delta\|\overline{\mathbf N}^s_\parallel\|^2]=0$ and is the starting point of the proof of Theorem 4: the left side is close to $\epsilon\,\mathbb E[\sum_{r,k}\kappa_r\overline N_{r,k}]$, the first term on the right is $o(1)$, and the last is pinned down by (86).
--
--   **Formalization Note** The printed (80) omits the closing angle brackets of both inner products (typo).
-- source:
--   Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, p. 30, (79)–(80)

import Mathlib
import Definitions.Def_HTInsensBW_PhaseType_Model
import Definitions.Def_HTInsensBW_PhaseType_InnerProduct

namespace HTInsensBW.PhaseType

open Matrix MeasureTheory

/-- **(80), p. 30 — the steady-state drift identity for `‖n^s_∥‖²`.** (Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, p. 30, (79)–(80).)
For `0 < ε < 1` and every stationary distribution `π` of the `ε`-th system, the three expectations
below are finite and
`ε E[⟨N̄^s_∥, (-Sᵀ)ρ^(0)⟩] = E[⟨N̄^s_∥, (-Sᵀ)(ρ^(0) - N̄x)⟩] + ½ E[B_1(N̄)]`,
where `n^s_∥` is the `M`-orthogonal projection of `n` onto the span of `b^(ℓ)`, `ℓ ∈ L_s`, and `B_1`
is the p. 30 term.

**Formalization Note** The standing hypotheses of §2 and §6 are explicit: `H` has 0/1 entries and full row rank
(p. 5); every route uses at least one link and every capacity is positive (implicit on p. 5 and in
(31): without them the allocation problem (2)–(4) has no optimum); `κ_r > 0` and `λ^(0)_r > 0`
(pp. 5, 7); `λ^(0)` is on the boundary of the capacity region, encoded as (7)–(8):
`Σ_{r : ℓ ∈ r} ρ^(0)_r ≤ C_ℓ` for all links with at least one link critical (`L_s ≠ ∅`); and `x` is
the weighted proportionally fair allocation (2)–(4), as a function of the route totals. The class
`D` (p. 22) is carried by the fields of `PhaseTypeD`.
The printed (80) drops the closing `⟩` of both inner products (typo). -/
theorem eq_80 {L R : ℕ} (N : BWNetwork L R)
    (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1) (hrank : N.H.rank = L)
    (hroute : ∀ r, ∃ ℓ, N.H ℓ r = 1) (hC : ∀ ℓ, 0 < N.C ℓ)
    (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r)
    (hload : ∀ ℓ, ∑ r, N.H ℓ r * routeLoad0 N r ≤ N.C ℓ) (hLs : (critical N).Nonempty)
    (x : (Fin R → ℕ) → Fin R → ℝ) (hx : ∀ m, IsWPFAllocation N m (x m)) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ π : State N → ℝ, IsStationary (rates N x ε) π →
      Summable (fun n => π n * mInner N (projS N (toReal N n)) ((-Sfull N)ᵀ *ᵥ rho0 N)) ∧
      Summable (fun n => π n *
        mInner N (projS N (toReal N n)) ((-Sfull N)ᵀ *ᵥ (rho0 N - nx N x n))) ∧
      Summable (fun n => π n * B1 N x ε n) ∧
      ε * ∑' n, π n * mInner N (projS N (toReal N n)) ((-Sfull N)ᵀ *ᵥ rho0 N) =
        ∑' n, π n * mInner N (projS N (toReal N n)) ((-Sfull N)ᵀ *ᵥ (rho0 N - nx N x n)) +
          (1 / 2) * ∑' n, π n * B1 N x ε n := by sorry

end HTInsensBW.PhaseType
