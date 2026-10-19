-- Prove2me | Theorems.Thm_HTInsensBW_PhaseType_eq_86
-- name    : HTInsensBW.PhaseType.eq_86
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:15:29.080308+00:00
-- url     : https://prove2.me/theorems/6c4ea78d-0090-45f2-ac91-3072ff20167f
-- title:
--   (86), p. 33 — (1 − ε)(min_r κ_r)Ls ≤ ½E[B1(N̄)] ≤ (1 − ε)(max_r κ_r)Ls
-- statement:
--   Under the standing assumptions of the paper (see Lemma 7), let $0<\epsilon<1$ and let $\overline{\mathbf N}$ be distributed as a stationary distribution of the $\epsilon$-th system, with $B_1$ the term of p. 30 and $L_s=|\mathcal L_s|$ the number of critically loaded links. Then $\mathbb E[B_1(\overline{\mathbf N})]$ is finite and
--   $$(1-\epsilon)\big(\min_r\kappa_r\big)L_s\ \le\ \tfrac12\,\mathbb E\big[B_1(\overline{\mathbf N})\big]\ \le\ (1-\epsilon)\big(\max_r\kappa_r\big)L_s .$$
--
--   This is where the leading constants of Theorem 4 come from: the trace computation (85)–(86) via Lemma 5 removes every dependence on the file-size laws except through the number of critical links.
--
--   **Formalization Note** The page proves the upper bound through (83)–(86) and states the lower bound with "Similarly"; the two-sided bound is posed.
-- source:
--   Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, pp. 32–33, (83)–(86) and the sentence after (86)

import Mathlib
import Definitions.Def_HTInsensBW_PhaseType_Model
import Definitions.Def_HTInsensBW_PhaseType_InnerProduct

namespace HTInsensBW.PhaseType

open Matrix MeasureTheory

/-- **(86) and its mirror, p. 33 — two-sided bound on `½ E[B_1(N̄)]`.**
(Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, pp. 32–33, (83)–(86) and the sentence after (86).)
For `0 < ε < 1` and every stationary distribution `π` of the `ε`-th system, `E[B_1(N̄)]` is finite
and `(1 - ε)(min_r κ_r) L_s ≤ ½ E[B_1(N̄)] ≤ (1 - ε)(max_r κ_r) L_s`, with `L_s = |L_s|`.

**Formalization Note** The standing hypotheses of §2 and §6 are explicit: `H` has 0/1 entries and full row rank
(p. 5); every route uses at least one link and every capacity is positive (implicit on p. 5 and in
(31): without them the allocation problem (2)–(4) has no optimum); `κ_r > 0` and `λ^(0)_r > 0`
(pp. 5, 7); `λ^(0)` is on the boundary of the capacity region, encoded as (7)–(8):
`Σ_{r : ℓ ∈ r} ρ^(0)_r ≤ C_ℓ` for all links with at least one link critical (`L_s ≠ ∅`); and `x` is
the weighted proportionally fair allocation (2)–(4), as a function of the route totals. The class
`D` (p. 22) is carried by the fields of `PhaseTypeD`.
The page proves the upper bound through (83)–(86) and states the lower one ("Similarly, …"); the
statement posed is the two-sided bound the proof concludes. -/
theorem eq_86 {L R : ℕ} (N : BWNetwork L R)
    (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1) (hrank : N.H.rank = L)
    (hroute : ∀ r, ∃ ℓ, N.H ℓ r = 1) (hC : ∀ ℓ, 0 < N.C ℓ)
    (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r)
    (hload : ∀ ℓ, ∑ r, N.H ℓ r * routeLoad0 N r ≤ N.C ℓ) (hLs : (critical N).Nonempty)
    (x : (Fin R → ℕ) → Fin R → ℝ) (hx : ∀ m, IsWPFAllocation N m (x m)) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ π : State N → ℝ, IsStationary (rates N x ε) π →
      Summable (fun n => π n * B1 N x ε n) ∧
      (1 - ε) * ((critical N).card : ℝ) * kappaMin N ≤ (1 / 2) * ∑' n, π n * B1 N x ε n ∧
      (1 / 2) * ∑' n, π n * B1 N x ε n ≤ (1 - ε) * ((critical N).card : ℝ) * kappaMax N := by sorry

end HTInsensBW.PhaseType
