-- Prove2me | Theorems.Thm_HTInsensBW_PhaseType_lemma_9
-- name    : HTInsensBW.PhaseType.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:15:21.87691+00:00
-- url     : https://prove2.me/theorems/980ff146-1950-461f-92cf-81c9b58bde8e
-- title:
--   Lemma 9, p. 31 — |α^s_ℓ − p_ℓ| ≤ B2‖n_⊥‖^{1/2}(Σ κ_r n_{r,k})^{1/2} on Ls and Σ_{ℓ∉Ls} p_ℓ ≤ B3‖n_⊥‖
-- statement:
--   Under the standing assumptions of the paper (see Lemma 7), there are positive constants $B_2$ and $B_3$ such that for every state $\mathbf n$ and every vector $(p_\ell)$ of Lagrange multipliers of the capacity constraints at $\mathbf n$ (nonnegative, complementary slack, and $x_r=\kappa_r/\sum_{\ell\in r}p_\ell$ on active routes),
--   $$|\alpha^s_\ell-p_\ell|\le B_2\|\mathbf n_\perp\|^{1/2}\Big(\sum_{r,k}\kappa_rn_{r,k}\Big)^{1/2}\quad\forall\ell\in\mathcal L_s,\qquad\sum_{\ell\in\mathcal L\setminus\mathcal L_s}p_\ell\le B_3\|\mathbf n_\perp\|,$$
--   where the $\alpha^s_\ell$ are the coefficients of the projection $\mathbf n^s_\parallel=\sum_{\ell\in\mathcal L_s}\alpha^s_\ell\mathbf b^{(\ell)}$.
--
--   It links the geometry of the state (its projection onto the subspace of the cone) to the prices $p_\ell$ of the allocation, and controls the first term of (80).
--
--   **Formalization Note** The multipliers need not be unique (empty routes leave freedom), so the bound is asserted for every multiplier vector.
-- source:
--   Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, p. 31, Lemma 9, (81)

import Mathlib
import Definitions.Def_HTInsensBW_PhaseType_Model
import Definitions.Def_HTInsensBW_PhaseType_InnerProduct

namespace HTInsensBW.PhaseType

open Matrix MeasureTheory

/-- **Lemma 9, p. 31.** (Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, p. 31, Lemma 9, (81).)
There are positive constants `B_2, B_3` such that for every state `n` and every vector `p` of
Lagrange multipliers of the capacity constraints at `n`:
`|α^s_ℓ - p_ℓ| ≤ B_2 ‖n_⊥‖^{1/2} (Σ_{r,k} κ_r n_{r,k})^{1/2}` for every `ℓ ∈ L_s`, and
`Σ_{ℓ ∈ L \ L_s} p_ℓ ≤ B_3 ‖n_⊥‖`, where `α^s` are the coefficients of the projection
`n^s_∥ = Σ_{ℓ ∈ L_s} α^s_ℓ b^(ℓ)`.

**Formalization Note** The standing hypotheses of §2 and §6 are explicit: `H` has 0/1 entries and full row rank
(p. 5); every route uses at least one link and every capacity is positive (implicit on p. 5 and in
(31): without them the allocation problem (2)–(4) has no optimum); `κ_r > 0` and `λ^(0)_r > 0`
(pp. 5, 7); `λ^(0)` is on the boundary of the capacity region, encoded as (7)–(8):
`Σ_{r : ℓ ∈ r} ρ^(0)_r ≤ C_ℓ` for all links with at least one link critical (`L_s ≠ ∅`); and `x` is
the weighted proportionally fair allocation (2)–(4), as a function of the route totals. The class
`D` (p. 22) is carried by the fields of `PhaseTypeD`.
The multipliers need not be unique (empty routes leave freedom); the bound is asserted for every
multiplier vector satisfying (5) with complementary slackness. Lemma 9 involves no `ε`. -/
theorem lemma_9 {L R : ℕ} (N : BWNetwork L R)
    (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1) (hrank : N.H.rank = L)
    (hroute : ∀ r, ∃ ℓ, N.H ℓ r = 1) (hC : ∀ ℓ, 0 < N.C ℓ)
    (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r)
    (hload : ∀ ℓ, ∑ r, N.H ℓ r * routeLoad0 N r ≤ N.C ℓ) (hLs : (critical N).Nonempty)
    (x : (Fin R → ℕ) → Fin R → ℝ) (hx : ∀ m, IsWPFAllocation N m (x m)) :
    ∃ B2 B3 : ℝ, 0 < B2 ∧ 0 < B3 ∧ ∀ (n : State N) (p : Fin L → ℝ),
      IsKKTMultiplier N (routeCount N n) (x (routeCount N n)) p →
      (∀ (ℓ : Fin L) (hℓ : ℓ ∈ critical N),
        |alphaS N (toReal N n) ⟨ℓ, hℓ⟩ - p ℓ| ≤
          B2 * Real.sqrt (perpNorm N (toReal N n)) * Real.sqrt (wsum N n)) ∧
      ∑ ℓ ∈ Finset.univ.filter (fun ℓ => ℓ ∉ critical N), p ℓ ≤
        B3 * perpNorm N (toReal N n) := by sorry

end HTInsensBW.PhaseType
