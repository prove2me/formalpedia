-- Prove2me | Theorems.Thm_ModularForm_logEta_modular_S_smul
-- name    : ModularForm.logEta_modular_S_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/1d37ac77-733c-57e9-b717-8579db981f1c
-- title:
--   Logarithmic S-transformation law for logη
-- statement:
--   Fix $z$ in the upper half-plane $\mathbb H$. Write $L(\tau)=\pi i\tau/12+\sum_{n\ge 0}\operatorname{Log}\bigl(1-q_n(\tau)\bigr)$ for the inlined expression `Real.pi * Complex.I * τ / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n τ)`, where $\tau$ is viewed in $\mathbb C$ through the coercion $\mathbb H\to\mathbb C$, $\operatorname{Log}$ is Mathlib's principal branch `Complex.log`, $q_n(\tau)=$ `ModularForm.eta_q n τ` $=e^{2\pi i(n+1)\tau}$, and the sum over $n:\mathbb N$ is an unconditional `tsum`. The assertion is the identity
--   $$L\bigl(S\cdot z\bigr)=L(z)+\tfrac12\operatorname{Log}(-i z),$$
--   an equality of complex numbers, where $S$ is `ModularGroup.S` acting on $\mathbb H$ by the Möbius action of $\mathrm{SL}_2(\mathbb Z)$, so that $S\cdot z=-1/z$, and $-iz$ denotes `-Complex.I * z` for the coerced $z\in\mathbb C$ (its real part is $\operatorname{Im}z>0$, so the principal logarithm is the natural branch). There are no hypotheses beyond $z\in\mathbb H$; in particular the branch of the logarithm on the right is pinned down, not merely determined up to $2\pi i\mathbb Z$.
--
--   This is the transformation law $\eta(-1/z)=\sqrt{-iz}\,\eta(z)$ lifted from $\eta$ to a fixed logarithm of $\eta$, with the additive constant determined exactly. It feeds the corresponding law for a general element of $\mathrm{SL}_2(\mathbb Z)$, [`ModularForm.logEta_specialLinearGroup_smul`](thm.html#ModularForm.logEta_specialLinearGroup_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_logEta_modular_S_smul.lean

import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.logEta_modular_S_smul (z : UpperHalfPlane) : (Real.pi * Complex.I * ((ModularGroup.S • z : UpperHalfPlane) : ℂ) / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n ((ModularGroup.S • z : UpperHalfPlane) : ℂ))) = (Real.pi * Complex.I * (z : ℂ) / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n (z : ℂ))) + Complex.log (-Complex.I * z) / 2 := by sorry
