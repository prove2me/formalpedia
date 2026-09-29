-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_isIntegral_jqN
-- name    : ModularCurve.ModularPolynomialData.isIntegral_jqN
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/28db7efc-0808-5a57-9883-8212753294ed
-- title:
--   j(q^N) is integral over ℚ(j(q))
-- statement:
--   Fix a natural number $N \neq 0$. Work inside the field of Laurent series $\mathbb{Q}((q))$ (`LaurentSeries ℚ`, Hahn series over $\mathbb{Q}$ with value group $\mathbb{Z}$), with the distinguished element $jq = q^{-1} \cdot jNumQ$, where $jNumQ$ is the integral power series $jNum$ pushed along $\mathbb{Z} \to \mathbb{Q}$, and with $jqN\,N = qExpand\,\mathbb{Q}\,N\,(jq)$, the image of $jq$ under the ring endomorphism of $\mathbb{Q}((q))$ induced by multiplication by $N$ on exponents, i.e. the substitution $q \mapsto q^N$. Assume given a datum `data : ModularPolynomialData N`, that is: a polynomial $\Phi \in (\mathbb{Z}[X])[Y]$ which is monic in $Y$, whose degree in $Y$ equals $\sum_{d \mid N,\ d \text{ squarefree}} N/d$, and which satisfies $\Phi(jq, jqN\,N) = 0$, the coefficients of $\Phi$ being evaluated at $jq$ through the ring homomorphism $evalAtJ : \mathbb{Z}[X] \to \mathbb{Q}((q))$, $X \mapsto jq$. The conclusion is that $jqN\,N$ is integral over the intermediate field $\mathbb{Q}\langle jq\rangle = \mathbb{Q}(jq) \subseteq \mathbb{Q}((q))$.
--
--   This is the integrality half of the classical statement that $\mathbb{Q}(j(q), j(q^N))$ is a finite extension of the rational function field $\mathbb{Q}(j(q))$, the modular equation $\Phi_N$ providing a monic relation for $j(q^N)$ over $\mathbb{Z}[j(q)]$. It is used in the construction of the Fricke involution on the algebraic model of $X_0(N)$, via [`ModularCurve.exists_isFrickeAut_of_modularPolynomialData`](thm.html#ModularCurve.exists_isFrickeAut_of_modularPolynomialData).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_isIntegral_jqN.lean

import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve IntermediateField

theorem ModularCurve.ModularPolynomialData.isIntegral_jqN {N : ℕ} [NeZero N] (data : ModularPolynomialData N) : IsIntegral ℚ⟮jq⟯ (jqN N) := by sorry
