-- Prove2me | Theorems.Thm_LefebvreVariations_lagrange_weights_degree_three
-- name    : LefebvreVariations.lagrange_weights_degree_three
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:26:38.485139+00:00
-- url     : https://prove2.me/theorems/66ee8d62-63bd-5bd8-a132-50f85967b787
-- title:
--   Lefebvre's variations, No. 272 — on a theme by Acheampong, Davis and Robere: four equally spaced Lagrange weights at zero are 4, -6, 4, -1 and extrapolate every cubic
-- statement:
--   Let $\omega^{(4)}_k=\prod_{j\in\{1,2,3,4\},\,j\ne k}\dfrac{-j}{k-j}$ be the Lagrange weight at $0$ of the node $k$ among the nodes $1,2,3,4$. Then
--   $$
--   \omega^{(4)}_1=4,\quad\omega^{(4)}_2=-6,\quad\omega^{(4)}_3=4,\quad\omega^{(4)}_4=-1,
--   $$
--   that is $\omega^{(4)}_k=(-1)^{k-1}\binom4k$, each $\omega^{(4)}_k$ equals $\ell_k(0)$ for the Lagrange basis $\ell_k$ of the nodes $1,2,3,4$, and every real polynomial $p$ of degree at most $3$ satisfies
--   $$
--   p(0)\;=\;4\,p(1)-6\,p(2)+4\,p(3)-p(4).
--   $$
--
--   This is the case $d=3$ ($d+1=4$ nodes) of the statement that, for polynomials of degree at most $d$, $p(0)=\sum_{k=1}^{d+1}(-1)^{k-1}\binom{d+1}{k}p(k)$, used to extrapolate to $0$ from the integer nodes $1,\dots,d+1$; equivalently, the fourth finite difference of a cubic vanishes.
--
--   **Formalization Note** The statement uses the platform definitions `omega` and `lagrangeBasis` of the `SAInterp.Res2` namespace: `omega m k = ∏ j ∈ (Finset.Icc 1 m).erase k, (-(j : ℝ)) / ((k : ℝ) - j)` and `lagrangeBasis t i = ∏ j ∈ univ.erase i, (X - C (t j)) * C (1 / (t i - t j))`, with the nodes `fun i : Fin 4 => (i.val : ℝ) + 1`, so the node `k + 1` is indexed by `k : Fin 4`. It combines the closed form of the weights, the identification with `ℓ_k(0)` and the exactness of the formula on `ℝ[X]` of degree at most `3`, as in `SAInterp.Res2.theorem_3_1` at `d = 3`.
--
--   **Why this is a variation.** This varies the open platform problem SAInterp.Res2.theorem_3_1 (Lagrange interpolation weights omega_k^(d+1) = (-1)^(k-1) C(d+1,k) at 0 for the nodes 1..d+1, and p(0) = sum of omega_k p(k) for degree at most d). It is the case d = 3, in the parent's own definitions omega and lagrangeBasis, with the four weights written out; the closed form is a finite product computation and the exactness is the vanishing of a fourth difference.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Origin of the statement: the case d = 3 of Theorem 3.1 of Acheampong, Davis and Robere, Polynomial interpolation for Sherali-Adams lower bounds (STOC 2027 submission as quoted on the platform parent SAInterp.Res2.theorem_3_1; not independently read). The weights are the binomial coefficients with alternating signs, i.e. the vanishing of the fourth forward finite difference of a polynomial of degree at most 3 (classical; checked by hand: weights 4, -6, 4, -1 from the product formula).

import Mathlib
import Definitions.Def_SAInterp_Res2_Interp

set_option autoImplicit false

open Polynomial SAInterp.Res2

namespace LefebvreVariations

/-- **Extrapolation to zero from four consecutive integer nodes.** The Lagrange weights of the nodes `1, 2, 3, 4`
at `0` are `ω = (4, −6, 4, −1)`, equal to `(−1)^{k−1} C(4, k)`, and every real polynomial `p` of degree at most `3`
satisfies `p(0) = 4p(1) − 6p(2) + 4p(3) − p(4)`. This is the case `d = 3` (`d + 1 = 4` nodes) of Theorem 3.1 of
Acheampong, Davis and Robere, *Polynomial interpolation for Sherali–Adams lower bounds* (as cited on the platform),
and equivalently the vanishing of the fourth finite difference of a cubic.

**Formalization Note.** Same `omega` and `lagrangeBasis` as `SAInterp.Res2.theorem_3_1` at `d = 3`, with the weights
written explicitly; the node `k ∈ [4]` is `k - 1 : Fin 4`. -/
theorem lagrange_weights_degree_three :
    (omega 4 1 = 4 ∧ omega 4 2 = -6 ∧ omega 4 3 = 4 ∧ omega 4 4 = -1) ∧
    (∀ k : Fin 4,
      omega 4 (k.val + 1) = (lagrangeBasis (fun i : Fin 4 => (i.val : ℝ) + 1) k).eval 0) ∧
    (∀ p : ℝ[X], p.natDegree ≤ 3 →
      p.eval 0 = 4 * p.eval 1 - 6 * p.eval 2 + 4 * p.eval 3 - p.eval 4) := by
  sorry

end LefebvreVariations
