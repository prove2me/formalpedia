-- Prove2me | Theorems.Thm_ModularCurve_isIntegral_jqNModC_of_mul
-- name    : ModularCurve.isIntegral_jqNModC_of_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/526e441b-bc03-558f-bcfa-8b1cb222e14e
-- title:
--   Integrality of j(qᵈ) over a field containing j(q^{dℓ})
-- statement:
--   Let $K$ be a field and let $F$ be an intermediate field of the Laurent series field $K((q))$ over $K$. Let $\ell$ and $d$ be nonzero natural numbers, and let `data` be a modular-polynomial datum of level $\ell$: a polynomial $\Phi \in (\mathbb{Z}[X])[Y]$ which is monic in $Y$, whose degree in $Y$ equals $\sum_{e \mid \ell,\ e \text{ squarefree}} \ell/e$, and which satisfies $\Phi(j(q), j(q^{\ell})) = 0$ in $\mathbb{Q}((q))$, evaluation of the coefficient polynomials being at the $q$-expansion $j(q)$. Assume in addition `EvalSymm data.Φ`, i.e. $\Phi$ is symmetric as an evaluation function on $\mathbb{Q}((q))$: for all $x, y \in \mathbb{Q}((q))$ one has $\Phi(x,y) = \Phi(y,x)$. Write `jqNModC K N` for the series in $K((q))$ obtained from the $q$-expansion $q^{-1}\sum_{n\ge 0} c_n q^{n}$ of $j$ with coefficients pushed into $K$ by substituting $q \mapsto q^{N}$ (multiplication of exponents by $N$). Assume $j_K(q^{d\ell}) =$ `jqNModC K (d * ℓ)` lies in $F$. Then `jqNModC K d` is integral over $F$.
--
--   This is the classical integrality statement attached to the modular equation: since the modular polynomial $\Phi_\ell$ is monic and symmetric, $j(q^{d})$ satisfies a monic equation with coefficients in any field containing $j(q^{d\ell})$. It supplies the integrality input for the degeneracy embeddings used to build the Hecke correspondence, being cited by [`ModularCurve.finiteAlong_heckeAlphaC`](thm.html#ModularCurve.finiteAlong_heckeAlphaC), [`ModularCurve.finiteAlong_heckeBetaC`](thm.html#ModularCurve.finiteAlong_heckeBetaC) and [`ModularCurve.heckeDivFibreDescends_of_separable_phi_map`](thm.html#ModularCurve.heckeDivFibreDescends_of_separable_phi_map).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isIntegral_jqNModC_of_mul.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.isIntegral_jqNModC_of_mul {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K)) {ℓ : ℕ} [NeZero ℓ] (data : ModularCurve.ModularPolynomialData ℓ) (hsymm : ModularCurve.EvalSymm data.Φ) (d : ℕ) [NeZero d] (hd : ModularCurve.jqNModC K (d * ℓ) ∈ F) : IsIntegral F (ModularCurve.jqNModC K d) := by sorry
