-- Prove2me | Theorems.Thm_ModularCurve_exists_monic_natDegree_le_aeval_jqModC_eq_zero
-- name    : ModularCurve.exists_monic_natDegree_le_aeval_jqModC_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/de9ac62f-e458-57da-86c9-2f43becae7bb
-- title:
--   Monic relation of degree ≤ p+1 for j over K(j(qᵖ))
-- statement:
--   Let $K$ be a field and $p$ a nonzero natural number. Inside the Laurent series field $K((q))$ put $\mathrm{jqModC}\,K = q^{-1}\cdot(E_4^3\,\eta^{-24})$, the $q$-expansion of $j$ with its integral coefficients mapped into $K$, and $\mathrm{jqNModC}\,K\,p$ its image under the substitution $q \mapsto q^{p}$ (the ring homomorphism `qExpand` induced by multiplication by $p$ on exponents). Assume given `data`, a record consisting of a polynomial $\Phi \in (\mathbb{Z}[X])[Y]$ together with proofs that $\Phi$ is monic in $Y$, that $\deg_Y \Phi$ equals $\psi(p) = \sum_{d \mid p,\ d \text{ squarefree}} p/d$, and that $\Phi$ vanishes when its $\mathbb{Z}[X]$-coefficients are evaluated at the rational series `jq` and $Y$ at `jqN p`. Assume further `EvalSymm` for $\Phi$: for all $x,y \in \mathbb{Q}((q))$, evaluating the coefficients at $x$ and $Y$ at $y$ gives the same result as evaluating the coefficients at $y$ and $Y$ at $x$; and assume $\psi(p) = p+1$. Then there is a monic polynomial $P$ over the intermediate field $K\big(\mathrm{jqNModC}\,K\,p\big) \subseteq K((q))$ with $\deg P \le p+1$ and $P(\mathrm{jqModC}\,K) = 0$.
--
--   This is the classical statement that the modular polynomial of level $p$, viewed as a polynomial in one variable with coefficients in $K(j(q^p))$, is monic of degree $\psi(p)$ and annihilates $j(q)$; the degree bound is recorded in the form $\le p+1$ for prime level. It is used to derive the integrality of $j(q)$ over $K(j(q^p))$ in [`ModularCurve.isIntegral_inclusion_adjoin_jqNModC`](thm.html#ModularCurve.isIntegral_inclusion_adjoin_jqNModC).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_monic_natDegree_le_aeval_jqModC_eq_zero.lean

import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_monic_natDegree_le_aeval_jqModC_eq_zero (K : Type*) [Field K] (p : ℕ) [NeZero p]
    (data : ModularCurve.ModularPolynomialData p) (hsym : ModularCurve.EvalSymm data.Φ)
    (hpsi : ModularCurve.dedekindPsi p = p + 1) :
    ∃ P : Polynomial (IntermediateField.adjoin K ({ModularCurve.jqNModC K p} :
        Set (LaurentSeries K))),
      P.Monic ∧ P.natDegree ≤ p + 1 ∧ Polynomial.aeval (ModularCurve.jqModC K) P = 0 := by sorry
