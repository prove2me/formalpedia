-- Prove2me | Theorems.Thm_HuWang2023_h0Diagnostic_const_iff
-- name    : HuWang2023.h0Diagnostic_const_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T00:47:27.962813+00:00
-- url     : https://prove2.me/theorems/15cc75b4-ebe6-4a99-bbea-6a121afb3db1
-- title:
--   Eq. (8): the $H_0(z)$ diagnostic is constant iff $H(z)$ is flat ΛCDM
-- statement:
--   Let $\Omega_{m0}\ge0$, $H_0\in\mathbb R$ and let $H:\mathbb R\to\mathbb R$ be any expansion history. The $H_0$ diagnostic of Eq. (8),
--   $$H_0(z) = \frac{H(z)}{\sqrt{1-\Omega_{m0}+\Omega_{m0}(1+z)^3}},$$
--   equals the constant $H_0$ for all $z\ge0$ if and only if
--   $$H(z) = H_0\sqrt{\Omega_{m0}(1+z)^3 + 1-\Omega_{m0}} \quad\text{for all } z\ge0,$$
--   that is, if and only if $H$ is the expansion history of flat ΛCDM with parameters $(H_0, \Omega_{m0})$.
--
--   This is why a redshift dependence ("running") of the diagnostic $H_0(z)$ signals a deviation from flat ΛCDM, as used in Section 5.
-- source:
--   Jian-Ping Hu and Fa-Yin Wang, *Hubble Tension: The Evidence of New Physics*, Universe 2023, 9(2), 94, https://doi.org/10.3390/universe9020094, Section 5, p. 14, Eq. (8) and the sentence following it

import Mathlib
import Definitions.Def_HuWang2023_HubbleTension_Defs

namespace HuWang2023

theorem h0Diagnostic_const_iff (Ωm0 H0 : ℝ) (H : ℝ → ℝ)
    (hΩm0 : 0 ≤ Ωm0) :
    (∀ z, 0 ≤ z → h0Diagnostic Ωm0 H z = H0) ↔ (∀ z, 0 ≤ z → H z = flatHubble H0 Ωm0 z) := by sorry

end HuWang2023
