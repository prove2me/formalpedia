-- Prove2me | Theorems.Thm_NewtonCartan_conn_eq_of_unitTimelike_quad
-- name    : NewtonCartan.conn_eq_of_unitTimelike_quad
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:58:00.045983+00:00
-- url     : https://prove2.me/theorems/22a274a5-f6f7-4e15-8218-7705460d127c
-- title:
--   Symmetric connection difference vanishing on unit timelike vectors is zero
-- statement:
--   Let $C^a{}_{bc}$ be symmetric in $b,c$. Suppose that for every unit-timelike vector $\xi^a$ (i.e. $t_a\xi^a=1$),
--   $$
--   C^a{}_{bc}\xi^b\xi^c=0.
--   $$
--   Then $C^a{}_{bc}=0$ identically.
--
--   This is the standard polarization of a quadratic form on the Newton–Cartan unit-timelike cone in a global chart on $\mathbb{R}^4$: expanding in spatial velocity $(p,q,r)$ yields a quadratic polynomial that vanishes for all $(p,q,r)$, hence all coefficients vanish.

import Definitions.Def_NewtonCartan_defs

open scoped ContDiff

namespace NewtonCartan

theorem conn_eq_of_unitTimelike_quad (C : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hsym : ∀ a b c, C a b c = C a c b)
    (hquad : ∀ a (ξ : Fin 4 → ℝ), ξ 0 = 1 →
      (∑ b : Fin 4, ∑ c : Fin 4, C a b c * ξ b * ξ c) = 0) :
    ∀ a b c, C a b c = 0 := by sorry

end NewtonCartan
