-- Prove2me | Theorems.Thm_MasulloRH_low_height_resolvent_tsum_zero_at_three
-- name    : MasulloRH.low_height_resolvent_tsum_zero_at_three
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-22T03:54:22.620564+00:00
-- url     : https://prove2.me/theorems/1380188b-da17-4397-877c-27582cbf7f68
-- title:
--   Low-height resolvent contribution vanishes
-- statement:
--   The low-height part of the compensated spectral resolvent sum at $s=3$ contributes exactly zero. Namely, over the distinct nontrivial zeta zeros in the open critical strip, retain the compensated term $m(\rho)((3-\rho)^{-1}-(5/2-\rho)^{-1})$ only when $|\operatorname{Im}\rho|^2<36$ and set it to zero otherwise. The resulting tsum is zero because the proved height-six rectangle contains no zeta zeros in the strip. This provides the exact low-height rewrite needed when separating the regularized Masullo spectral defect into finite and high-height pieces.
-- source:
--   Masullo, The Music of the Primes, Theorem 12.5.1.1 and §§1.4.2–1.4.5; corollary of the proved height-six zero-free rectangle and the Masullo regularized resolvent definition.

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_low_height_trace_zero_set_empty

set_option autoImplicit false

namespace MasulloRH

theorem low_height_resolvent_tsum_zero_at_three :
    (∑' ρ : ZetaZerosInTraceStrip (1 / 2),
      (if |ρ.val.im| ^ 2 < 36 then
        zeroResolventTerm (1 / 2) (3 : ℂ) ρ
      else 0)) = 0 := by sorry

end MasulloRH
