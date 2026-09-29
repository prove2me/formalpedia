-- Prove2me | Theorems.Thm_ModularCurve_exists_modularForm_coe_eq_discriminant_slash_heckeDiagMatrix
-- name    : ModularCurve.exists_modularForm_coe_eq_discriminant_slash_heckeDiagMatrix
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/8e80d8e8-ce1c-58aa-b2d0-63dea873af14
-- title:
--   Δ∣₁₂diag(p,1) is a modular form on Γ₀(p)
-- statement:
--   Let $p$ be a natural number, assumed nonzero. Write $\alpha_p :=$ [`ModularForm.heckeDiagMatrix p`](def/ModularForm_HeckeOperator.html#L21) for the element of $\mathrm{GL}_2(\mathbb{R})$ which, since $p \neq 0$, is the upper triangular matrix $!![p,0;0,1]$ viewed as an invertible real matrix via its nonzero determinant $p \cdot 1$ (for $p = 0$ the definition returns the identity, a case excluded by the hypothesis). The assertion is that there exists a modular form $D$ of weight $12$ for the congruence subgroup $\Gamma_0(p)$ whose underlying function $\mathbb{H} \to \mathbb{C}$ is equal to $\Delta \mid_{12} \alpha_p$, the weight-$12$ slash action of $\alpha_p$ applied to the function underlying the modular discriminant $\Delta$; with the determinant normalisation used for the slash action in weight $k = 12$, this function is $\tau \mapsto p^{11}\Delta(p\tau)$. So the content is that this translate of $\Delta$, a priori only a function on the upper half plane, satisfies weight-$12$ invariance under $\Gamma_0(p)$, is holomorphic, and is bounded at the cusps of $\Gamma_0(p)$.
--
--   This is the classical statement that the image of $\Delta$ under the degeneracy operator $V_p$ lies in the space of weight-$12$ modular forms on $\Gamma_0(p)$. It is used to compute $q$-expansion coefficients of $\Delta$-related forms of level $p$ and $p^2$, and hence in the divisibility statements about coefficients of cusp forms that feed the level-lowering input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_modularForm_coe_eq_discriminant_slash_heckeDiagMatrix.lean

import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Discriminant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped ModularForm

theorem ModularCurve.exists_modularForm_coe_eq_discriminant_slash_heckeDiagMatrix (p : ℕ) [NeZero p] : ∃ D : ModularForm (CongruenceSubgroup.Gamma0 p) 12, ⇑D = ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix p := by sorry
