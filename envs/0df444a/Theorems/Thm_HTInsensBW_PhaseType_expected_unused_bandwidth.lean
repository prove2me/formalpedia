-- Prove2me | Theorems.Thm_HTInsensBW_PhaseType_expected_unused_bandwidth
-- name    : HTInsensBW.PhaseType.expected_unused_bandwidth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:37.784325+00:00
-- url     : https://prove2.me/theorems/314acbc9-2929-42e6-a1d4-fcd2293f8f5a
-- title:
--   Proof of Theorem 4, p. 32 — E[U_ℓ] = εC_ℓ for every critically loaded link
-- statement:
--   Under the standing assumptions of the paper (see Lemma 7), let $0<\epsilon<1$ and let $\overline{\mathbf N}$ be distributed as a stationary distribution of the $\epsilon$-th system. For every critically loaded link $\ell\in\mathcal L_s$, the expected unused bandwidth $U_\ell=C_\ell-\sum_{r:\ell\in r}\overline N_rx_r$ is finite and
--   $$\mathbb E[U_\ell]=\epsilon\,C_\ell .$$
--
--   It is used to bound the second term of (80).
--
--   **Formalization Note** The paper derives it from $\Delta w_\ell=-\epsilon C_\ell+U_\ell$, which uses $\delta_\ell=0$; it is therefore stated for $\ell\in\mathcal L_s$, which is how the proof uses it (for other links the same argument gives $\mathbb E[U_\ell]=\delta_\ell+\epsilon(C_\ell-\delta_\ell)$).
-- source:
--   Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, p. 32, proof of Theorem 4, step (ii)

import Mathlib
import Definitions.Def_HTInsensBW_PhaseType_Model

namespace HTInsensBW.PhaseType

/-- **`E[U_ℓ] = ε C_ℓ`, p. 32.** (Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, p. 32, proof of Theorem 4, step (ii).)
For `0 < ε < 1`, every stationary distribution `π` of the `ε`-th system and every critically
loaded link `ℓ ∈ L_s`, the expected unused bandwidth is finite and equals `ε C_ℓ`.

**Formalization Note** The standing hypotheses of §2 and §6 are explicit: `H` has 0/1 entries and full row rank
(p. 5); every route uses at least one link and every capacity is positive (implicit on p. 5 and in
(31): without them the allocation problem (2)–(4) has no optimum); `κ_r > 0` and `λ^(0)_r > 0`
(pp. 5, 7); `λ^(0)` is on the boundary of the capacity region, encoded as (7)–(8):
`Σ_{r : ℓ ∈ r} ρ^(0)_r ≤ C_ℓ` for all links with at least one link critical (`L_s ≠ ∅`); and `x` is
the weighted proportionally fair allocation (2)–(4), as a function of the route totals. The class
`D` (p. 22) is carried by the fields of `PhaseTypeD`.
The page derives `Δw_ℓ = -ε C_ℓ + U_ℓ` using `δ_ℓ = 0`, so the identity is for `ℓ ∈ L_s`, which
is how the proof uses it (for other links `E[U_ℓ] = δ_ℓ + ε (C_ℓ - δ_ℓ)`). -/
theorem expected_unused_bandwidth {L R : ℕ} (N : BWNetwork L R)
    (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1) (hrank : N.H.rank = L)
    (hroute : ∀ r, ∃ ℓ, N.H ℓ r = 1) (hC : ∀ ℓ, 0 < N.C ℓ)
    (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r)
    (hload : ∀ ℓ, ∑ r, N.H ℓ r * routeLoad0 N r ≤ N.C ℓ) (hLs : (critical N).Nonempty)
    (x : (Fin R → ℕ) → Fin R → ℝ) (hx : ∀ m, IsWPFAllocation N m (x m)) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ π : State N → ℝ, IsStationary (rates N x ε) π →
      ∀ ℓ ∈ critical N, Summable (fun n => π n * unused N x n ℓ) ∧
        ∑' n, π n * unused N x n ℓ = ε * N.C ℓ := by sorry

end HTInsensBW.PhaseType
