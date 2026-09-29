-- Prove2me | Theorems.Thm_ModularCurve_swapBivar_monic_of_coeff_bounds
-- name    : ModularCurve.swapBivar_monic_of_coeff_bounds
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/22506f9c-ecfa-59f1-b51a-fd80256fe722
-- title:
--   Monicity of the transpose under coefficient degree bounds
-- statement:
--   Let $\Phi$ be a polynomial in one variable over $\mathbb{Z}[X]$, i.e. $\Phi \in (\mathbb{Z}[X])[Y]$, and let $d$ be a natural number. Assume: the constant coefficient $\Phi_0 = \Phi.\mathrm{coeff}\ 0 \in \mathbb{Z}[X]$ is monic with $\deg \Phi_0 = d$; and for every index $k \neq 0$ the coefficient $\Phi_k = \Phi.\mathrm{coeff}\ k$ satisfies $\deg \Phi_k < d$ as an inequality in $\mathbb{N} \cup \{\bot\}$, so that in particular $\Phi_k = 0$ is permitted (and forced when $d = 0$). Here `swapBivar` is the ring endomorphism of $(\mathbb{Z}[X])[Y]$ obtained by evaluating a polynomial $\sum_k \Phi_k Y^k$ at $Y \mapsto C(X)$ with coefficients mapped by `swapInner`, the ring homomorphism $\mathbb{Z}[X] \to (\mathbb{Z}[X])[Y]$ sending the variable $X$ to the outer variable $Y$; thus `swapBivar` is the transposition interchanging the two variables. The conclusion is that $\mathrm{swapBivar}\ \Phi$ is monic as a polynomial in the outer variable and that its degree equals $d$.
--
--   This is the elementary coefficient bookkeeping behind the statement that a bivariate polynomial whose constant row dominates all other rows in degree becomes, after interchanging the two variables, monic of the same degree in the new outer variable. It is used in the treatment of the symmetry of the modular polynomials, in [`ModularCurve.ModularPolynomialData.evalSymm_of_one_lt`](thm.html#ModularCurve.ModularPolynomialData.evalSymm_of_one_lt) and [`ModularCurve.ModularPolynomialData.evalSymm_of_squarefree`](thm.html#ModularCurve.ModularPolynomialData.evalSymm_of_squarefree).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_swapBivar_monic_of_coeff_bounds.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.swapBivar_monic_of_coeff_bounds {Φ : Polynomial (Polynomial ℤ)} {d : ℕ} (h0 : (Φ.coeff 0).Monic) (h0deg : (Φ.coeff 0).natDegree = d) (hk : ∀ k, k ≠ 0 → (Φ.coeff k).degree < (d : WithBot ℕ)) : (swapBivar Φ).Monic ∧ (swapBivar Φ).natDegree = d := by sorry
