-- Prove2me | Theorems.Thm_MegiddoLP_FixedDim_dependent_pair
-- name    : MegiddoLP.FixedDim.dependent_pair
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:09:59.108985+00:00
-- url     : https://prove2.me/theorems/fd09fbe0-5f0f-45dc-9c1e-5f641f4f40d7
-- title:
--   A linearly dependent pair of opposite slopes: $a_{i1}=a_{k1}=0$ and the middle hyperplane settles one of them
-- statement:
--   Let $d\ge2$, let $H_i=\{a_i^Tx=b_i\}$ have nonnegative slope and $H_k=\{a_k^Tx=b_k\}$ nonpositive slope, and suppose the two are linearly dependent: $a_i=\lambda a_k$ for a real $\lambda\neq0$. Then:
--
--   1. $a_{i1}=a_{k1}=0$;
--   2. let $H^{(1)}_{ik}$ be the hyperplane midway between them,
--
--   $$H^{(1)}_{ik}:\ \sum_j a_{ij}x_j=\tfrac12(b_i+\lambda b_k).$$
--
--   There is a rule $F$, depending only on the data, that maps the oracle's answer for $H^{(1)}_{ik}$ to one of $H_i$, $H_k$ and a position, such that for every $x\in\mathbb{R}^d$ the position is the true position of $x$ relative to that hyperplane.
--
--   Part 1 holds because a dependent pair has a common slope, which must be both nonnegative and nonpositive, hence $0$. Part 2 shows that in the dependent case a single hyperplane with zero $x_1$-coefficient replaces the pair $H^{(1)}_{ik}$, $H^{(2)}_{ik}$. So the recursion into dimension $d-1$ also covers this case.
--
--   **Formalization Note** The dimension is $d+2$ in Lean and $x_1$ is index `0`. $\lambda$ is written `lam`.
-- source:
--   Megiddo, Linear Programming in Linear Time When the Dimension Is Fixed, J. ACM 31(1) (1984) 114–127, §3.2, p. 120 and Figure 2 (the linearly dependent case)

import Mathlib
import Definitions.Def_MegiddoLP_FixedDim_Pairing

/-!
Megiddo, J. ACM 31 (1984), §3.2 p. 120 (Figure 2): a linearly dependent pair of hyperplanes of
opposite slopes has zero `x₁`-coefficients, and the hyperplane midway between them settles
the position of `x*` relative to one of the two. The paper's `x₁, x₂` are the indices `0, 1`
of `Fin (d + 2)`.
-/

namespace MegiddoLP.FixedDim

/-- **The linearly dependent pair.** Let `Hᵢ = {aᵢ ⬝ᵥ x = bᵢ}` have nonnegative slope and
`H_k = {a_k ⬝ᵥ x = b_k}` nonpositive slope, with `aᵢ = λ a_k` for a real `λ ≠ 0`. Then
`a_i1 = a_k1 = 0`, and there is a rule `F`, depending only on the data, mapping the oracle's
answer for the middle hyperplane `H⁽¹⁾_ik = {aᵢ ⬝ᵥ x = (bᵢ + λ b_k)/2}` to a choice of `Hᵢ`
(`true`) or `H_k` (`false`) and the correct position of `x` relative to it, for every `x`. -/
theorem dependent_pair {d : ℕ} (ai ak : Fin (d + 2) → ℝ) (bi bk lam : ℝ)
    (hlam : lam ≠ 0) (hdep : ai = lam • ak)
    (hi : HasNonnegSlope ai) (hk : HasNonposSlope ak) :
    (ai 0 = 0 ∧ ak 0 = 0) ∧
    ∃ F : Ordering → Bool × Ordering, ∀ x : Fin (d + 2) → ℝ,
      let r := F (compare (ai ⬝ᵥ x) ((bi + lam * bk) / 2))
      (r.1 = true → compare (ai ⬝ᵥ x) bi = r.2) ∧
      (r.1 = false → compare (ak ⬝ᵥ x) bk = r.2) := by sorry

end MegiddoLP.FixedDim
