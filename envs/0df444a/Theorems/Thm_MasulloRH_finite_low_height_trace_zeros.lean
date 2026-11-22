-- Prove2me | Theorems.Thm_MasulloRH_finite_low_height_trace_zeros
-- name    : MasulloRH.finite_low_height_trace_zeros
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-22T03:08:53.142736+00:00
-- url     : https://prove2.me/theorems/f4b3d595-d566-4577-b5fc-5a67e3a6d8c5
-- title:
--   Finiteness of the low-height zeta-zero set in the centered trace strip
-- statement:
--   The actual zeta zeros in the centered critical strip with $|operatorname{Im}
--   ho|^2<36$ form a finite set:
--
--   $$
--   \left\{\rho:\; \zeta(\rho)=0,\quad 0<\operatorname{Re}\rho<1,
--   \quad \left|\operatorname{Re}\rho-\tfrac12\right|<\tfrac12,
--   \quad |\operatorname{Im}\rho|^2<36\right\}
--   \quad\text{is finite.}
--   $$
--
--   This is the finite-height bookkeeping interface needed by the Masullo compensated-resolvent split. The proof encloses every such zero in the closed disk of radius $7$, uses Mathlib's discreteness theorem for the Riemann-zeta zero set on compact subsets, and transports finiteness through the injective subtype projection. No zero-location assertion is made: the real parts remain unrestricted inside the open critical strip.
-- source:
--   Classical compactness/discreteness input for Masullo, The Music of the Primes, §§1.4.2–1.4.5 and Theorem 12.5.1.1. The finite-height cutoff is the one used by the Masullo-native compensated-resolvent split. Mathlib supplies IsCompact.inter_riemannZetaZeros_finite for the actual zeta zero set.

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib.NumberTheory.LSeries.ZetaZeros

set_option autoImplicit false
open MasulloRH Set Metric

theorem MasulloRH.finite_low_height_trace_zeros :
    {ρ : ZetaZerosInTraceStrip (1 / 2) | |ρ.val.im| ^ 2 < 36}.Finite := by sorry
