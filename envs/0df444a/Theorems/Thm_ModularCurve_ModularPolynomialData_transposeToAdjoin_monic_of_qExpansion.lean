-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_transposeToAdjoin_monic_of_qExpansion
-- name    : ModularCurve.ModularPolynomialData.transposeToAdjoin_monic_of_qExpansion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/6b155394-313a-5c59-926d-42044b44adeb
-- title:
--   Transpose of Φ monic of degree ψ(N) over ℚ(j)
-- statement:
--   Fix a positive level $N$ and let `data` be a modular-polynomial packet at level $N$: a bivariate polynomial $\Phi \in (\mathbb{Z}[X])[Y]$ which is monic in $Y$, of $Y$-degree $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$, and which satisfies $\Phi(j, j_N) = 0$, where the inner variable is specialised through the ring map `evalAtJ` sending $X$ to the Laurent $q$-series $jq$ and the outer variable to the series `jqN N`. Write $\Phi = \sum_k \Phi_k(X)\,Y^k$ with $\Phi_k \in \mathbb{Z}[X]$. Assume three conditions on the $q$-expansions $\Phi_k(jq) \in$ `LaurentSeries ℚ`: the coefficient of $\Phi_0(jq)$ in degree $-\psi(N)$ equals $1$; for every natural $m > \psi(N)$ the coefficient of $\Phi_0(jq)$ in degree $-m$ vanishes; and for every $k \neq 0$ and every natural $m \geq \psi(N)$ the coefficient of $\Phi_k(jq)$ in degree $-m$ vanishes. Then the transposed polynomial `swapBivar data.Φ`, obtained by interchanging the two variables, with coefficients mapped into the simple extension $\mathbb{Q}(jq)$ by evaluation of $\mathbb{Z}[X]$ at the generator $jq$, is monic and has degree exactly $\psi(N)$.
--
--   This records the classical degree and leading-coefficient statement for the modular equation read in the other variable: the pole orders of the $q$-expansions $\Phi_k(j)$, together with the simplicity of the pole of $j$, pin down the $X$-degree of $\Phi$ as $\psi(N)$ and its leading $X$-coefficient as $1$. It is used by [`ModularCurve.PhiGen.evalSymm_of_coeff_evalAtJ_eq`](thm.html#ModularCurve.PhiGen.evalSymm_of_coeff_evalAtJ_eq) in establishing the symmetry properties of the modular polynomial over $\mathbb{Q}(j)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_transposeToAdjoin_monic_of_qExpansion.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.ModularPolynomialData.transposeToAdjoin_monic_of_qExpansion {N : ℕ} [NeZero N] (data : ModularPolynomialData N) (h0top : (evalAtJ (data.Φ.coeff 0)).coeff (-(dedekindPsi N : ℤ)) = 1) (h0le : ∀ m : ℕ, dedekindPsi N < m → (evalAtJ (data.Φ.coeff 0)).coeff (-(m : ℤ)) = 0) (hk : ∀ k, k ≠ 0 → ∀ m : ℕ, dedekindPsi N ≤ m → (evalAtJ (data.Φ.coeff k)).coeff (-(m : ℤ)) = 0) : ((swapBivar data.Φ).map evalAtJGen).Monic ∧ ((swapBivar data.Φ).map evalAtJGen).natDegree = dedekindPsi N := by sorry
