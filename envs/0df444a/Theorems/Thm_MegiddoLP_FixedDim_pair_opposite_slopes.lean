-- Prove2me | Theorems.Thm_MegiddoLP_FixedDim_pair_opposite_slopes
-- name    : MegiddoLP.FixedDim.pair_opposite_slopes
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:09:34.175985+00:00
-- url     : https://prove2.me/theorems/3ec1eaf2-fb15-493d-a929-f4741b0b40af
-- title:
--   Positions relative to $H^{(1)}_{ik}$ and $H^{(2)}_{ik}$ determine the position relative to $H_i$ or $H_k$
-- statement:
--   Let $d\ge2$, let $H_i=\{x\in\mathbb{R}^d: a_i^Tx=b_i\}$ have nonnegative slope and $H_k=\{x: a_k^Tx=b_k\}$ nonpositive slope in the $(x_1,x_2)$ plane, and assume
--
--   $$\delta=a_{k1}a_{i2}-a_{k2}a_{i1}\ne0.$$
--
--   Let $H^{(1)}_{ik}$ and $H^{(2)}_{ik}$ be the paired hyperplanes. Then there is a rule $F$, depending only on $a_i,a_k,b_i,b_k$, that takes the two oracle answers (the position of $x$ relative to $H^{(1)}_{ik}$ and relative to $H^{(2)}_{ik}$) and returns one of the two hyperplanes $H_i$, $H_k$ together with a position. For every point $x\in\mathbb{R}^d$ the returned position is the true position of $x$ relative to the returned hyperplane.
--
--   This is the claim of p. 119 that "if we know the position of $x^*$ relative to both of these hyperplanes, then we can readily tell the position of $x^*$ relative to one of either $H_i$ or $H_k$". Because the slopes have opposite signs, each pair of queries settles one member of each pair of hyperplanes.
--
--   **Formalization Note** The dimension is $d+2$ in Lean and $x_1,x_2$ are the indices `0, 1`. The hypothesis $\delta\ne0$ is the one the page's argument uses ("depending on the sign of $a_{k1}a_{i2}-a_{k2}a_{i1}$"). The page's own hypothesis, "the defining equations of $H_i$ and $H_k$ are linearly independent", does not imply $\delta\ne0$: $a_i=(0,1,1)$ and $a_k=(0,1,0)$ are independent, both have slope $0$, and $\delta=0$. Under the section's standing normalisation (p. 119: a basis in which $a_{ij}\ne0$ for all $i,j$), opposite slopes are nonzero and distinct, so $\delta=a_{i2}a_{k2}(s_i-s_k)\ne0$; the hypothesis $\delta\ne0$ therefore holds in the setting where the page applies the claim. The page's displayed inequalities print $b_n$ where $b_k$ is meant, and the Lean uses $b_k$. The rule $F$ returns a flag (`true` for $H_i$, `false` for $H_k$) and an `Ordering`.
-- source:
--   Megiddo, Linear Programming in Linear Time When the Dimension Is Fixed, J. ACM 31(1) (1984) 114–127, §3.2, pp. 119–120 and Figure 1 (the pairing argument)

import Mathlib
import Definitions.Def_MegiddoLP_FixedDim_Pairing

/-!
Megiddo, J. ACM 31 (1984), §3.2 pp. 119–120 (Figure 1): if `Hᵢ` has nonnegative slope and
`H_k` nonpositive slope, then the positions of `x*` relative to `H⁽¹⁾_ik` and `H⁽²⁾_ik`
determine its position relative to one of `Hᵢ`, `H_k`. The paper's `x₁, x₂` are the indices
`0, 1` of `Fin (d + 2)`.
-/

namespace MegiddoLP.FixedDim

/-- **The pairing claim.** Let `Hᵢ = {aᵢ ⬝ᵥ x = bᵢ}` have nonnegative slope and
`H_k = {a_k ⬝ᵥ x = b_k}` nonpositive slope in the `(x₁, x₂)` plane, with
`a_k1 a_i2 - a_k2 a_i1 ≠ 0`. There is a rule `F`, depending only on the data, which maps the
oracle's answers for `H⁽¹⁾_ik` and `H⁽²⁾_ik` to a choice of `Hᵢ` (`true`) or `H_k` (`false`)
together with the correct position of `x` relative to the chosen hyperplane, for every `x`. -/
theorem pair_opposite_slopes {d : ℕ} (ai ak : Fin (d + 2) → ℝ) (bi bk : ℝ)
    (hi : HasNonnegSlope ai) (hk : HasNonposSlope ak)
    (hdet : ak 0 * ai 1 - ak 1 * ai 0 ≠ 0) :
    ∃ F : Ordering → Ordering → Bool × Ordering, ∀ x : Fin (d + 2) → ℝ,
      let r := F (compare (pairNormal1 ai ak ⬝ᵥ x) (pairRhs1 ai ak bi bk))
                 (compare (pairNormal2 ai ak ⬝ᵥ x) (pairRhs2 ai ak bi bk))
      (r.1 = true → compare (ai ⬝ᵥ x) bi = r.2) ∧
      (r.1 = false → compare (ak ⬝ᵥ x) bk = r.2) := by sorry

end MegiddoLP.FixedDim
