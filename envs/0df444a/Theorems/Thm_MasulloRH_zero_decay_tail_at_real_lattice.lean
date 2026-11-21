-- Prove2me | Theorems.Thm_MasulloRH_zero_decay_tail_at_real_lattice
-- name    : MasulloRH.zero_decay_tail_at_real_lattice
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:08:22.13922+00:00
-- url     : https://prove2.me/theorems/7bc6a754-4e26-454c-8292-b565c7f0247c
-- title:
--   An explicit logarithmic height bound for the full multiplicity-weighted zeta zero tail
-- statement:
--   For $n\ge0$, put $H=5/2+2n$, $L=\zeta'/\zeta$, and $A=\Re(L(3)-L(5/2)-\operatorname{Arch}(3)+\operatorname{Polar}(3))$. Summing over distinct nontrivial zeta zeros $\rho=\beta+i\gamma$ with analytic multiplicities $m_\rho$, one has
--   $$\sum_{|\gamma|>H}\frac{m_\rho}{1+\gamma^2}\le\frac{2}{H-1}\left(8A-\Re L(5/2)+\frac{1+\log n}{2}\right).$$
--   At $n=0$ take $\log 0=0$. For $n\ge1$ this is an explicit $O((\log H)/H)$ estimate for the full zero tail in Masullo’s regularized trace, including both signs of the ordinate.
-- source:
--   Quantitative specialization of the proved full-strip regularized zeta trace identity and weighted-zero summability. Uses the independently certified zero-free rectangle to ordinate six and the real-shift recurrence of the archimedean term.

import Definitions.Def_MasulloRH_RegularizedTrace

set_option autoImplicit false

namespace MasulloRH

theorem zero_decay_tail_at_real_lattice (n : ℕ) :
    let H : ℝ := 5/2+2*n
    (∑' z : ZetaZerosInTraceStrip (1/2),
      if H < |z.val.im| then zeroDecayWeight (1/2) z else 0) ≤
    2/(H-1) * (8*((zetaLogDeriv 3).re -
      (zetaLogDeriv (5/2)+regularizedArch 3-regularizedPolar 3).re) -
      (zetaLogDeriv (5/2)).re + (1+Real.log n)/2) := by sorry

end MasulloRH
