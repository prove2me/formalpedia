-- Prove2me | Theorems.Thm_ModularCurve_exists_genus_riemannIndex_modularFunctionFieldBar
-- name    : ModularCurve.exists_genus_riemannIndex_modularFunctionFieldBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/bdee9ae5-0eb7-5c98-b299-1d1fe68a3fa9
-- title:
--   Riemann–Roch index identity for the modular function field of X₀(N)
-- statement:
--   Fix a natural number $N \neq 0$, and let $F_N$ denote `modularFunctionFieldBar N`: the intermediate field of the Laurent series field $\overline{\mathbb Q}((q))$ over $\overline{\mathbb Q}$ obtained by adjoining to $\overline{\mathbb Q}$ the image, under the coefficientwise embedding $\mathbb Q((q)) \to \overline{\mathbb Q}((q))$, of the full level-$N$ modular function field `modularFunctionFieldFull N`, itself the subfield of $\mathbb Q((q))$ generated over $\mathbb Q$ by the family `divisorExpansions N`. The assertion is that there exists an integer $\gamma$ such that for every divisor $D$ of $F_N$ over $\overline{\mathbb Q}$ — that is, every finitely supported $\mathbb Z$-valued function on the places of $F_N/\overline{\mathbb Q}$, a place being a proper valuation subring of $F_N$ containing $\overline{\mathbb Q}$ whose valuation ring is a principal ideal ring — two statements hold. First, the quotient of the adele space $\mathbb A$ (the supremum over all divisors $E$ of the submodules $\{\alpha : \forall v,\ v(\alpha_v) \le \exp(E(v))\}$ of $\prod_v F_N$) by the sum of the preimages in $\mathbb A$ of $\mathbb A(D)$ and of the diagonal copy of $F_N$ is a finite-dimensional $\overline{\mathbb Q}$-vector space. Second, its dimension, the index of speciality $i(D)$, satisfies $i(D) = \ell(D) - (\deg D + 1 - \gamma)$, where $\ell(D)$ is the $\overline{\mathbb Q}$-dimension of the Riemann–Roch space of $D$ and $\deg D = \sum_v D(v)\,\deg v$.
--
--   This is the Riemann–Roch theorem in index form, with $\gamma$ playing the role of the genus, for the function field of the modular curve $X_0(N)$ base-changed to $\overline{\mathbb Q}$; in particular it records that $\ell(D)$ is finite for every divisor and fixes the genus as a single integer invariant of the field. It supplies the dimension-counting input for the geometry of this modular function field used later in the construction of points and chords on the associated curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_genus_riemannIndex_modularFunctionFieldBar.lean

import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.exists_genus_riemannIndex_modularFunctionFieldBar (N : ℕ) [NeZero N] :
    ∃ γ : ℤ, ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      Module.Finite (AlgebraicClosure ℚ) (↥(adeleSpace (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) ⧸ adeleBddPrincipal (AlgebraicClosure ℚ) (modularFunctionFieldBar N) D) ∧
        (indexOfSpecialty D : ℤ) = (ell D : ℤ) - (Divisor.degree D + 1 - γ) := by sorry
