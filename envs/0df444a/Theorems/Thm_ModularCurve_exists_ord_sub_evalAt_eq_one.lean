-- Prove2me | Theorems.Thm_ModularCurve_exists_ord_sub_evalAt_eq_one
-- name    : ModularCurve.exists_ord_sub_evalAt_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/e9aa2290-19b5-5002-95d2-3bc81ee65862
-- title:
--   Model coordinates give uniformisers away from the cusp
-- statement:
--   Let $N$ be a positive natural number and let $\bar F_N$ denote `modularFunctionFieldBar N`, the intermediate field of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise images of the subfield $\mathbb Q(\mathrm{divisorExpansions}\,N)$ of $\mathbb Q((q))$. Let $r$ be a natural number and $s : \mathrm{Fin}\,r \to \bar F_N$ a family satisfying `IsEmbBasis N s`, that is: $s$ is linearly independent over $\overline{\mathbb Q}$ and its range spans the Riemann–Roch space $\{f : \mathrm{ord}_v f \ge -D(v) \text{ for all places } v\}$ of the divisor $D = (\mathrm{embDegree}\,N)\cdot \bar\infty$, where $\bar\infty$ is the $q$-adic cusp `cuspInftyBar N`. Let $R$ be a place of $\bar F_N$ over $\overline{\mathbb Q}$ — a proper valuation subring of $\bar F_N$ containing $\overline{\mathbb Q}$ which is a principal ideal ring — and suppose $R \ne \bar\infty$. Then there is an index $i$ such that $s_i$ lies in the valuation ring of $R$ and $$\mathrm{ord}_R\bigl(s_i - s_i(R)\bigr) = 1,$$ where $s_i(R) \in \overline{\mathbb Q}$ is the image of $s_i$ in the residue field of $R$ pulled back along $\overline{\mathbb Q} \to \kappa(R)$ and then viewed as a constant function.
--
--   This is the separation-of-tangent-vectors half of the very ampleness of the complete linear system $|(\mathrm{embDegree}\,N)\bar\infty|$ on $X_0(N)$: the coordinate functions of the chosen projective model furnish, at every point other than the base cusp, a uniformiser of the shape $x - x(R)$. It is used in the height-form estimates for the model, being cited by [`ModularCurve.JZero.exists_baseMass_le_heightForm_of_exists_two_le`](thm.html#ModularCurve.JZero.exists_baseMass_le_heightForm_of_exists_two_le), where a uniformiser drawn from a fixed finite family of functions makes the constants in local Taylor expansions uniform in the point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ord_sub_evalAt_eq_one.lean

import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_ord_sub_evalAt_eq_one (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hR : R ≠ cuspInftyBar N) :
    ∃ i, s i ∈ R.toValuationSubring ∧
      R.ord (s i - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (R.evalAt (s i))) = 1 := by sorry
