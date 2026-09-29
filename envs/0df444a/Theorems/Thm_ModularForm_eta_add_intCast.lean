-- Prove2me | Theorems.Thm_ModularForm_eta_add_intCast
-- name    : ModularForm.eta_add_intCast
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/2ac7c8b0-ae52-5d37-8c0b-6709038a2489
-- title:
--   Translation of η by an integer
-- statement:
--   Let $z$ be a complex number and $m$ an integer. The assertion is that Mathlib's Dedekind eta function `ModularForm.eta`, regarded as a function of a complex variable — the $q$-parameter $\mathrm{qParam}\,24\,z = e^{2\pi i z/24}$ times the infinite product $\prod_{n\ge 0}\bigl(1 - e^{2\pi i (n+1) z}\bigr)$ — satisfies the translation law
--   $$\eta(z+m) = e^{\pi i m/12}\,\eta(z),$$
--   where the exponential factor is $\exp(\pi \cdot i \cdot m/12)$ with $\pi$ the real circle constant coerced to $\mathbb{C}$ and $m$ coerced from $\mathbb{Z}$. Thus no positivity or upper-half-plane condition is imposed on $z$, and the integer $m$ may be of either sign; the equality is an identity of complex numbers holding for all $(z,m) \in \mathbb{C} \times \mathbb{Z}$. In particular the multiplier is the $24$-th root of unity $e^{2\pi i m/24}$, so $\eta$ is invariant under $z \mapsto z + 24$.
--
--   This is the elementary half of the transformation behaviour of the Dedekind eta function, namely its behaviour under the translation generator $T^m$ of $\mathrm{SL}_2(\mathbb{Z})$. It feeds the derivation of the full transformation law [`ModularForm.eta_specialLinearGroup_smul`](thm.html#ModularForm.eta_specialLinearGroup_smul) under $\mathrm{SL}_2(\mathbb{Z})$, and through it the unit invariant [`ModularCurve.sharpUnitInvariant`](thm.html#ModularCurve.sharpUnitInvariant) on the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_eta_add_intCast.lean

import Mathlib.NumberTheory.ModularForms.DedekindEta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.eta_add_intCast (z : ℂ) (m : ℤ) : ModularForm.eta (z + m) = Complex.exp (Real.pi * Complex.I * m / 12) * ModularForm.eta z := by sorry
