-- Prove2me | Theorems.Thm_HuWang2023_timeDelayDistance_determines_H0
-- name    : HuWang2023.timeDelayDistance_determines_H0
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T00:48:12.911986+00:00
-- url     : https://prove2.me/theorems/edb0e7c0-613d-4619-a3bb-0f78ba15a5ef
-- title:
--   Quasar lensing: the time-delay distance determines $H_0$
-- statement:
--   Fix the speed of light $c>0$, a matter density parameter $\Omega_m \ge 0$ of a flat ΛCDM universe, and lens and source redshifts with $0 < z_{\rm lens} < z_s$. Then there is a constant $K>0$, depending only on $c$, $\Omega_m$, $z_{\rm lens}$, $z_s$, such that for every Hubble constant $H_0>0$ the time-delay distance (Eq. (1)) satisfies
--   $$D_{\Delta t}(H_0) = \frac{K}{H_0}.$$
--
--   In particular $H_0 = K/D_{\Delta t}$ is uniquely recovered from a measured time-delay distance once the redshifts and $\Omega_m$ are fixed. This is the mathematical content of the statement in Section 3.1 that "with observed time delay and lens mass model, $H_0$ can be inferred" and that the time-delay distance is "primarily sensitive to $H_0$".
--
--   **Formalization Note** The time-delay distance is built from the angular diameter distances of Eqs. (2)–(3) (with the standard integrand $1/E(z')$). The constraint $\Omega_m \le 1$ (non-negative $\Omega_\Lambda$) is not needed and is omitted.
-- source:
--   Jian-Ping Hu and Fa-Yin Wang, *Hubble Tension: The Evidence of New Physics*, Universe 2023, 9(2), 94, https://doi.org/10.3390/universe9020094, Section 3.1 Quasar Lensing, p. 4, Eqs. (1)–(3) and the sentence following Eq. (3)

import Mathlib
import Definitions.Def_HuWang2023_HubbleTension_Defs

namespace HuWang2023

theorem timeDelayDistance_determines_H0 (c Ωm zl zs : ℝ) (hc : 0 < c)
    (hΩm0 : 0 ≤ Ωm) (hzl : 0 < zl) (hzls : zl < zs) :
    ∃ K : ℝ, 0 < K ∧ ∀ H0 : ℝ, 0 < H0 → timeDelayDistance c H0 Ωm zl zs = K / H0 := by sorry

end HuWang2023
