-- Prove2me | Theorems.Thm_ModularCurve_PhiGen_evalSymm_of_splits
-- name    : ModularCurve.PhiGen.evalSymm_of_splits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/bd35dbad-dce7-57a0-a3be-bfe56ea31d43
-- title:
--   Symmetry of Φ_ℓ from its splitting into conjugates
-- statement:
--   Let $K$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $\ell$ be a prime, and let $\zeta \in K^\times$ be such that $\zeta$ is a primitive $\ell$-th root of unity in $K$. Let `data` be a modular-polynomial packet of level $\ell$, that is, a polynomial $\Phi \in \mathbb{Z}[X][Y]$ that is monic in $Y$, of degree $\psi(\ell) = \sum_{d \mid \ell,\ d \text{ squarefree}} \ell/d$, and satisfies $\Phi(j, j_{(\ell)}) = 0$ after substituting the $q$-expansion $jq$ of the modular invariant for $X$. Three hypotheses are assumed. First, applying to the coefficients of $\Phi$ the composite $X \mapsto jq$, then the exponent-scaling map `qExpand ℚ ℓ`, then the coefficient extension $\mathbb{Q} \to K$, yields the polynomial $\prod_{i \in \mathrm{Fin}(\ell+1)} \bigl(Y - \mathrm{conj}\,\ell\,\zeta\,i\bigr)$ over the Laurent series over $K$, where the $i$-th conjugate is obtained from $jq$ over $K$ by the twist `qTwist (ζ ^ (a * b))` followed by multiplication of exponents by $a^2$, with $(a,b) = (\ell, 0)$ for $i = 0$ and $(a,b) = (1, i-1)$ otherwise. Second, the transpose `swapBivar data.Φ`, mapped by $X \mapsto$ the generator $j$ of $\mathbb{Q}\langle jq\rangle$, is monic. Third, that transpose has degree at most $\psi(\ell)$. The conclusion is `EvalSymm data.Φ`: for all Laurent series $x, y$ over $\mathbb{Q}$, $\Phi(x,y) = \Phi(y,x)$.
--
--   This is the classical symmetry $\Phi_N(X,Y) = \Phi_N(Y,X)$ of the modular polynomial, in the case of prime level, derived here from the splitting of $\Phi_\ell$ into the product over the $\ell+1$ conjugates together with degree and monicity control on the transpose. It feeds the criterion [`ModularCurve.PhiGen.evalSymm_of_coeff_evalAtJ_eq`](thm.html#ModularCurve.PhiGen.evalSymm_of_coeff_evalAtJ_eq), which reduces the symmetry to a comparison of coefficients after evaluation at the $q$-expansion of $j$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PhiGen_evalSymm_of_splits.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.PhiGen.evalSymm_of_splits {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) (data : ModularPolynomialData ℓ) (hsplit : data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ) = phiProd ℓ (conj ℓ ζ)) (hTmonic : ((swapBivar data.Φ).map evalAtJGen).Monic) (hTdeg : ((swapBivar data.Φ).map evalAtJGen).natDegree ≤ dedekindPsi ℓ) : EvalSymm data.Φ := by sorry
