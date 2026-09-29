-- Prove2me | Theorems.Thm_ModularCurve_JZero_divNaiveHeight_le_baseMass_of_isRepOf
-- name    : ModularCurve.JZero.divNaiveHeight_le_baseMass_of_isRepOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/64a14d32-8217-5d4e-a75e-c1f8255f175d
-- title:
--   Naive height of a representative bounded by base mass
-- statement:
--   Fix a level $N$ (nonzero), a subfield $K$ of $\overline{\mathbb Q}$ containing $\mathbb Q$ and finite over it, a natural number $g'$, and a finite family $s \colon \mathrm{Fin}\,r \to \overline{\mathbb Q}\cdot F_N$ of elements of the geometric modular function field `modularFunctionFieldBar N` (the base change to $\overline{\mathbb Q}$ of the full modular function field of level $N$ inside Laurent series) which is an `IsEmbBasis`, that is: $s$ is linearly independent over $\overline{\mathbb Q}$ and its span is the Riemann–Roch space $\{f : v(f) \le \exp(D(v)) \text{ for all places } v\}$ of the divisor `embDivisor N` $= \mathrm{embDegree}(N)\cdot[\,\infty\,]$ supported at the cusp `cuspInftyBar N`. Then there are real numbers $\kappa \ge 0$ and $C$, depending only on these data, such that for every class $c$ in the part of $\mathrm{Pic}^0$ of `modularFunctionFieldBar N` over $\overline{\mathbb Q}$ fixed by the subgroup of $\mathrm{Aut}(\overline{\mathbb Q}/\mathbb Q)$ fixing $K$ pointwise, and every divisor $D$ on the places of `modularFunctionFieldBar N` over $\overline{\mathbb Q}$ which represents $c$ in the sense of `IsRepOf N K g'` — namely there is a degree-zero divisor $E$ with $D$ effective, $E + g'\cdot[\,\infty\,] = D$, with $D$ invariant under the arithmetic Galois action of every $\sigma$ fixing $K$, and with the class of $E$ in $\mathrm{Pic}^0$ equal to $c$ — one has
--   $$\mathrm{divNaiveHeight}\,N\,K\,g'\,D \le \kappa\,\mathrm{baseMass}\,N\,s\,D + C,$$
--   where the left-hand side is the logarithmic height over $K$ of the coefficient vector $(\mathrm{symPoly}\,N\,D)_{g'-k}$, $k \in \mathrm{Fin}(g'+1)$, when all these coefficients lie in $K$ (and is $0$ otherwise), and $\mathrm{baseMass}\,N\,s\,D = \sum_{v \ne \infty} D(v)\cdot \mathrm{pairHt}\,s\,v\,\infty$.
--
--   This is the upper comparison estimate between the naive height attached to a Galois-stable effective representative divisor and the intrinsic base mass of that divisor away from the cusp, in the style of the Néron–Mumford comparisons of naive and canonical heights. It is used by [`ModularCurve.JZero.exists_isRepOf_heightForm_lower`](thm.html#ModularCurve.JZero.exists_isRepOf_heightForm_lower) to pass from naive-height information to a lower bound for the height form on the fixed part of $\mathrm{Pic}^0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_divNaiveHeight_le_baseMass_of_isRepOf.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_ModularCurve_JZeroHeightFormPositivity
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem ModularCurve.JZero.divNaiveHeight_le_baseMass_of_isRepOf (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (g' : ℕ) {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ κ C : ℝ, 0 ≤ κ ∧
      ∀ (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        IsRepOf N K g' c D →
        divNaiveHeight N K g' D ≤ κ * baseMass N s D + C := by sorry
