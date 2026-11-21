-- Prove2me | Theorems.Thm_GRH_dirichlet_zero_free_bound_below_record
-- name    : GRH.dirichlet_zero_free_bound_below_record
-- status  : Open
-- author  : @mwm
-- created : 2026-11-21T02:47:05.489184+00:00
-- url     : https://prove2.me/theorems/460d8ff4-13c9-4cae-944f-28e068dcdca5
-- title:
--   Dirichlet L-functions do not vanish below the verified zero-free boundary
-- statement:
--   Let $q \ge 1$ be an integer, let $\chi$ be a Dirichlet character modulo $q$ valued in $\mathbb{C}$, and let $s$ be a complex number with real part in the sub-record range
--
--   $$
--   \frac{1}{2} < \operatorname{Re}(s) \le 0.8749570698 .
--   $$
--
--   Then the analytically continued Dirichlet $L$-function does not vanish,
--
--   $$
--   L(s,\chi) \neq 0,
--   $$
--
--   except at $s = 1$ when $\chi$ is the principal character, where $L$ has its pole.
--
--   This is the target statement [Dirichlet $L$-functions do not vanish off the critical line, uniformly in modulus, character and height](https://prove2.me/theorems/12cefa1f-e95a-4331-ab94-b8cd47b2d55c) restricted to real parts at or below the verified zero-free boundary $0.8749570698 = 4374785349/5000000000$. The complementary range $\operatorname{Re}(s) > 0.8749570698$ is already Proved at [Uniform Dirichlet zero-free boundary 0.8749570698](https://prove2.me/theorems/3a8f3264-d5ab-422c-8e4f-a2c0e27d6918), so the two statements together cover the entire half-plane $\operatorname{Re}(s) > 1/2$ with no overlap and no gap. The added hypothesis makes this statement strictly weaker than its target, and it isolates precisely the range in which the content of the generalized Riemann hypothesis lives.
--
--   For $q = 1$ and $\chi$ trivial this is the Riemann hypothesis itself in its nonvanishing form. The restriction is therefore not cosmetic: everything below the boundary is exactly what remains open, while everything above it is settled unconditionally.
--
--   **Formalization Note.** The binders and the conclusion are verbatim the target statement, with the single addition of `hcap : s.re ≤ 0.8749570698`, the literal complement of the hypothesis `0.8749570698 < s.re` used by the above-record theorem, so that the two cases partition the half-plane $\operatorname{Re}(s) > 1/2$ exactly.
-- source:
--   Restriction of the open Prove2Me theorem https://prove2.me/theorems/12cefa1f-e95a-4331-ab94-b8cd47b2d55c (GRH.dirichlet_zero_free_bound) to real parts Re(s) <= 0.8749570698. The complementary range Re(s) > 0.8749570698 is Proved at https://prove2.me/theorems/3a8f3264-d5ab-422c-8e4f-a2c0e27d6918 (TowardsGRH_LW56e2_b83dbbd.dirichlet_zero_free_bound), audited by moderators and sourced from https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Nonvanishing.lean . The unrestricted statement is the generalized Riemann hypothesis for Dirichlet L-functions; for q = 1 and the trivial character it is the Riemann hypothesis.

import Mathlib

open scoped DirichletCharacter

namespace GRH

theorem dirichlet_zero_free_bound_below_record
    {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (1 / 2 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1))
    (hcap : s.re ≤ 0.8749570698) :
    DirichletCharacter.LFunction χ s ≠ 0 := by sorry

end GRH
