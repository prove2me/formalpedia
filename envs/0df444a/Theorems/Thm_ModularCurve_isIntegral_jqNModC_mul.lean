-- Prove2me | Theorems.Thm_ModularCurve_isIntegral_jqNModC_mul
-- name    : ModularCurve.isIntegral_jqNModC_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/96f96f04-8e46-51b3-a977-a0fcc82d4859
-- title:
--   Integrality of j(q^{dℓ}) over fields containing j(qᵈ)
-- statement:
--   Let $K$ be a field and let $F$ be an intermediate field of the extension $K((q))/K$, where $K((q))$ is the field `LaurentSeries K` of formal Laurent series. Let $\ell$ and $d$ be nonzero natural numbers, and let `data` be a modular-polynomial datum of level $\ell$: a polynomial $\Phi \in (\mathbb{Z}[X])[Y]$ which is monic in $Y$, whose degree in $Y$ equals the Dedekind $\psi$-value $\sum_{e \mid \ell,\ e\ \text{squarefree}} \ell/e$, and which satisfies $\Phi(j(q), j(q^{\ell})) = 0$ in $\mathbb{Q}((q))$, the substitution of $j(q)$ for $X$ being `evalAtJ` and $j(q^{\ell})$ the series `jqN ℓ`. Here, for a nonzero natural number $N$, the element `jqNModC K N` of $K((q))$ is obtained from the $q$-expansion $q^{-1}\cdot(\text{numerator series of } j)$ with coefficients reduced into $K$ by substituting $q \mapsto q^{N}$, i.e. by the ring embedding `qExpand` which multiplies all exponents by $N$. Assume `jqNModC K d` lies in $F$. Then `jqNModC K (d * ℓ)` is integral over $F$.
--
--   This is the classical statement that $j(q^{d\ell})$ satisfies a monic equation over any field of Laurent series containing $j(q^{d})$, obtained from the modular equation $\Phi_{\ell}(X,Y)$ being monic in $Y$. It is one of the integrality inputs for the degeneracy maps used in the construction of the Hecke correspondence, and is cited in the finiteness and field-degree statements for the relevant adjunctions of $q$-expansions, such as [`ModularCurve.finiteAlong_heckeAlphaBar_of_modularPolynomialData`](thm.html#ModularCurve.finiteAlong_heckeAlphaBar_of_modularPolynomialData) and [`ModularCurve.finrank_adjoin_jqNModC_igusaFunctionFieldX1C_eq`](thm.html#ModularCurve.finrank_adjoin_jqNModC_igusaFunctionFieldX1C_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isIntegral_jqNModC_mul.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.isIntegral_jqNModC_mul {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K)) {ℓ : ℕ} [NeZero ℓ] (data : ModularCurve.ModularPolynomialData ℓ) (d : ℕ) [NeZero d] (hd : ModularCurve.jqNModC K d ∈ F) : IsIntegral F (ModularCurve.jqNModC K (d * ℓ)) := by sorry
