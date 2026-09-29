-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_irreducible
-- name    : ModularCurve.ModularPolynomialData.evalSymm_of_irreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/e86cfe7b-d249-50b0-aca3-047cc0375c73
-- title:
--   Evaluation symmetry of an irreducible modular polynomial datum
-- statement:
--   Fix a natural number $N$ with $N \neq 0$ and let `data` be a modular polynomial datum at level $N$: a bivariate integral polynomial $\Phi \in \mathbb{Z}[X][Y]$ (outer variable $Y$, coefficients in $\mathbb{Z}[X]$) which is monic in $Y$, has $Y$-degree equal to $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$, and satisfies $\Phi(j(q), j(q^N)) = 0$ in the field of Laurent series $\mathbb{Q}((q))$, where $j(q)$ is the $q$-expansion `jq` of the modular invariant and $j(q^N)$ is `jqN N`. Three further hypotheses are imposed. First, `PhiIrreducible data`: the image of $\Phi$ in $\mathbb{Q}(j(q))[Y]$, obtained by evaluating each coefficient polynomial at the generator $j(q)$ of the simple extension $\mathbb{Q}\langle j(q)\rangle$ of $\mathbb{Q}$ inside $\mathbb{Q}((q))$, is irreducible. Second, the transposed polynomial $\Phi(Y, X)$, formed by the variable-swapping ring homomorphism `swapBivar`, also vanishes after the substitution $X \mapsto j(q^N)$, $Y \mapsto j(q)$, i.e. $\Phi(j(q^N), j(q)) = 0$. Third, the image of the transpose in $\mathbb{Q}(j(q))[Y]$ is monic, and its degree is at most $\psi(N)$. The conclusion is `EvalSymm data.Φ`: for all Laurent series $x, y \in \mathbb{Q}((q))$ one has $\Phi(x,y) = \Phi(y,x)$, the substitution being taken coefficientwise via $\mathbb{Z}$-algebra evaluation.
--
--   This is the classical symmetry $\Phi_N(X,Y) = \Phi_N(Y,X)$ of the modular equation of level $N$, obtained here from irreducibility together with the degree and monicity bounds, which force $\Phi$ and its transpose to be the same minimal polynomial of $j(q^N)$ over $\mathbb{Q}(j(q))$. It is the general step behind [`ModularCurve.ModularPolynomialData.evalSymm_of_one_lt`](thm.html#ModularCurve.ModularPolynomialData.evalSymm_of_one_lt) and [`ModularCurve.ModularPolynomialData.evalSymm_of_squarefree`](thm.html#ModularCurve.ModularPolynomialData.evalSymm_of_squarefree), which supply the irreducibility and degree hypotheses in the cases of interest.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_evalSymm_of_irreducible.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.ModularPolynomialData.evalSymm_of_irreducible {N : ℕ} [NeZero N] (data : ModularPolynomialData N) (hirr : PhiIrreducible data) (hswap : data.Φ.eval₂ (evalAtJqN N) jq = 0) (hTmonic : ((swapBivar data.Φ).map evalAtJGen).Monic) (hTdeg : ((swapBivar data.Φ).map evalAtJGen).natDegree ≤ dedekindPsi N) : EvalSymm data.Φ := by sorry
