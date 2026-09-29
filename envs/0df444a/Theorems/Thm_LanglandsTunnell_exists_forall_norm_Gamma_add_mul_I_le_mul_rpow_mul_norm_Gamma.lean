-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_forall_norm_Gamma_add_mul_I_le_mul_rpow_mul_norm_Gamma
-- name    : LanglandsTunnell.exists_forall_norm_Gamma_add_mul_I_le_mul_rpow_mul_norm_Gamma
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/2b603498-f79f-54bb-a2c7-939946a87b6a
-- title:
--   A crude bound for |Γ(y+d+iτ')/Γ(y+iτ)|
-- statement:
--   For arbitrary real numbers $d$, $\tau$, $\tau'$ there exist real constants $K$ and $R$ with $K>0$ such that for every real $y$ with $y\ge R$ one has
--   $$\bigl\|\Gamma\bigl((y+d)+i\tau'\bigr)\bigr\| \le K\,y^{d}\,\bigl\|\Gamma(y+i\tau)\bigr\|,$$
--   where $\Gamma$ is the complex Gamma function (`Complex.Gamma`), the arguments are the complex numbers obtained from the real points $y+d$ and $y$ shifted by $i\tau'$ and $i\tau$ respectively, $\|\cdot\|$ is the complex absolute value, and $y^{d}$ denotes the real power $y\mapsto y^{d}$ (real `rpow`). No sign or size condition is imposed on $d$, $\tau$, $\tau'$; the shift $d$ may be negative or non-integral. Only this one-sided inequality is asserted, valid in the stated half-line $y\ge R$; no asymptotic equivalence, no explicit value of $K$ or $R$, and no positivity of $R$ are claimed (although the $R$ produced by the proof is positive).
--
--   This is a crude one-sided form of the archimedean estimate $|\Gamma(y+d+i\tau')/\Gamma(y+i\tau)|\sim y^{d}$ as $y\to+\infty$ with $\tau,\tau'$ fixed, in the shape needed for dominance and ratio arguments. It is used in bounding the Mellin transform occurring in [`LanglandsTunnell.norm_mellin_gaussTorusTransform_halfStep_le`](thm.html#LanglandsTunnell.norm_mellin_gaussTorusTransform_halfStep_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_forall_norm_Gamma_add_mul_I_le_mul_rpow_mul_norm_Gamma.lean

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.exists_forall_norm_Gamma_add_mul_I_le_mul_rpow_mul_norm_Gamma
    (d τ τ' : ℝ) :
    ∃ K R : ℝ, 0 < K ∧ ∀ y : ℝ, R ≤ y →
      ‖Complex.Gamma (((y + d : ℝ) : ℂ) + (τ' : ℂ) * Complex.I)‖
        ≤ K * y ^ d * ‖Complex.Gamma ((y : ℂ) + (τ : ℂ) * Complex.I)‖ := by sorry
