-- Prove2me | Theorems.Thm_MasulloRH_high_height_resolvent_norm_summable_at_three
-- name    : MasulloRH.high_height_resolvent_norm_summable_at_three
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-22T03:48:41.528356+00:00
-- url     : https://prove2.me/theorems/195b8e00-0752-48e2-926e-c39b488c9839
-- title:
--   Summable high-height compensated resolvent tail
-- statement:
--   At the real probe $s=3$, the compensated resolvent terms from the height range $|\operatorname{Im}\rho|^2\ge36$ form an absolutely summable family. Explicitly, for each distinct nontrivial zero $\rho$ in the open critical strip, retain the norm of the compensated term $m(\rho)((3-\rho)^{-1}-(5/2-\rho)^{-1})$ when its squared ordinate is at least $36$, and set the term to zero below that threshold. The resulting nonnegative family is summable. This is the high-height component of the Masullo regularized spectral defect; the complementary low-height component is empty by the proved height-six zero-free rectangle.
-- source:
--   Masullo, The Music of the Primes, Theorem 12.5.1.1 and §§1.4.2–1.4.5; corollary of the proved full-strip compensated-resolvent summability theorem.

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_full_strip_resolvent_norm_summable_at_three

set_option autoImplicit false

namespace MasulloRH

theorem high_height_resolvent_norm_summable_at_three :
    Summable (fun ρ : ZetaZerosInTraceStrip (1 / 2) =>
      if 36 ≤ |ρ.val.im| ^ 2 then
        ‖zeroResolventTerm (1 / 2) (3 : ℂ) ρ‖
      else 0) := by sorry

end MasulloRH
