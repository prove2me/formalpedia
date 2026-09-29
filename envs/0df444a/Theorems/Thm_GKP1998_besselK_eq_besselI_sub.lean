-- Prove2me | Theorems.Thm_GKP1998_besselK_eq_besselI_sub
-- name    : GKP1998.besselK_eq_besselI_sub
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T00:52:51.530245+00:00
-- url     : https://prove2.me/theorems/829202db-2d51-4468-a2ab-9513125eab84
-- title:
--   Eq. (42): $K_\nu=\frac{\pi}{2\sin\pi\nu}(I_{-\nu}-I_\nu)$ for non-integer $\nu$
-- statement:
--   For every real $\nu\notin\mathbb Z$ and $x>0$,
--   $$K_\nu(x)=\frac{\pi}{2\sin(\pi\nu)}\big(I_{-\nu}(x)-I_\nu(x)\big).$$
-- source:
--   S.S. Gubser, I.R. Klebanov, A.M. Polyakov, Gauge theory correlators from non-critical string theory, Phys. Lett. B 428 (1998) 105-114, arXiv:hep-th/9802109, p. 112, Eq. (42)

import Definitions.Def_GKP1998_Defs

open Filter Topology Asymptotics

namespace GKP1998
/-- Eq. (42), first display: for non-integer `ν` and `x > 0`,
`K_ν(x) = π / (2 sin(πν)) · (I_{−ν}(x) − I_ν(x))`. -/
theorem besselK_eq_besselI_sub (ν x : ℝ) (hν : ∀ n : ℤ, ν ≠ n) (hx : 0 < x) :
    besselK ν x = Real.pi / (2 * Real.sin (Real.pi * ν)) * (besselI (-ν) x - besselI ν x) := by
  sorry
end GKP1998
