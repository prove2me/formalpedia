-- Prove2me | Theorems.Thm_ModularForm_exists_gamma0_four_apply_eq_apply_two_smul
-- name    : ModularForm.exists_gamma0_four_apply_eq_apply_two_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/355f4080-8c6d-500b-9be9-04408c3e2bde
-- title:
--   A level-one form read at 2z lies on Γ₀(4)
-- statement:
--   Let $k$ be an integer and let $f$ be a modular form of weight $k$ for the group $\mathcal{SL}$, i.e. for the image of $\mathrm{SL}_2(\mathbb{Z})$ inside $\mathrm{GL}_2(\mathbb{R})$ regarded as a subgroup (so $f$ is a holomorphic function on the upper half-plane $\mathbb{H}$, weight-$k$ invariant under that subgroup and bounded at the cusps). There are no further hypotheses. The assertion is that there exists a modular form $g$ of the same weight $k$ for the subgroup of $\mathrm{GL}_2(\mathbb{R})$ attached to the congruence subgroup $\Gamma_0(4)$ of $\mathrm{SL}_2(\mathbb{Z})$ — thus $g$ is holomorphic on $\mathbb{H}$, satisfies the weight-$k$ transformation law under $\Gamma_0(4)$ and is bounded at the cusps of $\Gamma_0(4)$ — such that for every $z \in \mathbb{H}$ one has $g(z) = f(2 \cdot z)$, where $2 \cdot z$ denotes the action of the positive real number $2$ on the upper half-plane, that is, $g(z) = f(2z)$. Since the argument only uses that the lower-left entry of an element of $\Gamma_0(4)$ is even, the conclusion stated for $\Gamma_0(4)$ is weaker than the corresponding statement for $\Gamma_0(2)$.
--
--   This is the degeneracy (or scaling) map $f \mapsto f(2z)$ from level one to level $4$, in the form of an existence statement for the target form. It is used in the verification of the identity $E_4(z)\eta(z)^8 = \eta(z/2)^{16} + 16\,\eta(z/2)^8\eta(2z)^8 + 256\,\eta(2z)^{16}$ recorded in [`ModularForm.E4_mul_eta_pow_eight_eq`](thm.html#ModularForm.E4_mul_eta_pow_eight_eq), where $f = E_4\Delta$ of weight $16$ is read at $2z$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_gamma0_four_apply_eq_apply_two_smul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularForm.exists_gamma0_four_apply_eq_apply_two_smul {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    ∃ g : ModularForm (CongruenceSubgroup.Gamma0 4) k,
      ∀ z : UpperHalfPlane, g z = f ((⟨2, two_pos⟩ : {x : ℝ // 0 < x}) • z) := by sorry
