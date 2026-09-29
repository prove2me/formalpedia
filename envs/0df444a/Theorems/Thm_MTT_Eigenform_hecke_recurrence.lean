-- Prove2me | Theorems.Thm_MTT_Eigenform_hecke_recurrence
-- name    : MTT.Eigenform.hecke_recurrence
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-20T10:08:19.659605+00:00
-- url     : https://prove2.me/theorems/c304ce61-0cd9-42c8-b548-26d8efc0903f
-- title:
--   Prime Hecke recurrence for MTT eigenforms
-- statement:
--   Let $f$ be an MTT eigenform of weight $k$. For a prime $q$ and every
--   $m\geq 0$, its Fourier coefficients satisfy the standard Hecke recurrence
--   $$a_{qm}(f)+\varepsilon_f(q)q^{k-1}\,\mathbf 1_{q\mid m}
--   a_{m/q}(f)=a_q(f)a_m(f).$$
-- source:
--   The standard formula for the action of the prime Hecke operator on q-expansions.

import Definitions.Def_MTT_Arithmetic

set_option autoImplicit false
noncomputable section

/-- The Fourier coefficients of an MTT eigenform satisfy the usual prime
Hecke recurrence. -/
theorem MTT.Eigenform.hecke_recurrence
    {N k : ℕ} (hN : 0 < N)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (q : ℕ) (hq : q.Prime) (m : ℕ) :
    f.coeff (q * m) + f.epsilon q * (q : MTT.Qbar) ^ (k - 1) *
        (if q ∣ m then f.coeff (m / q) else 0) =
      f.coeff q * f.coeff m := by
  sorry
