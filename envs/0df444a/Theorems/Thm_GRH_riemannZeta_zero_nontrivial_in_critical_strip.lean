-- Prove2me | Theorems.Thm_GRH_riemannZeta_zero_nontrivial_in_critical_strip
-- name    : GRH.riemannZeta_zero_nontrivial_in_critical_strip
-- status  : Proved
-- author  : @LG
-- created : 2026-11-21T16:11:51.366791+00:00
-- url     : https://prove2.me/theorems/1cd52b08-9d82-47ea-b033-b008081c62f2
-- title:
--   Nontrivial zeros of ζ lie in the critical strip
-- statement:
--   Every zero $s$ of the Riemann zeta function that is not one of its trivial zeros lies in the open critical strip:
--
--   $$0<\operatorname{Re}(s)<1.$$
--
--   The upper bound follows from the non-vanishing of $\zeta(s)$ on $\operatorname{Re}(s)\ge1$. The lower bound is the zero-classification consequence of the functional equation: in $\operatorname{Re}(s)\le0$, zeros are precisely the trivial zeros $-2(n+1)$. This lemma isolates the boundary analysis needed to reduce the full nontrivial-zero formulation to the critical-strip theorem for the primitive character modulo $1$.
-- source:
--   Mathlib 4.33.1 (revision 0df444a360ea): Mathlib/NumberTheory/LSeries/RiemannZeta.lean, riemannZeta_one_sub; Mathlib/NumberTheory/LSeries/Nonvanishing.lean, riemannZeta_ne_zero_of_one_le_re. https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries

import Mathlib

namespace GRH

theorem riemannZeta_zero_nontrivial_in_critical_strip {s : ℂ}
    (hz : riemannZeta s = 0)
    (htriv : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) :
    0 < s.re ∧ s.re < 1 := by sorry

end GRH
