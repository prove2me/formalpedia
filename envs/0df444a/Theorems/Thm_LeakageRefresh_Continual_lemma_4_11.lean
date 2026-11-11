-- Prove2me | Theorems.Thm_LeakageRefresh_Continual_lemma_4_11
-- name    : LeakageRefresh.Continual.lemma_4_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:09:02.47487+00:00
-- url     : https://prove2.me/theorems/7691825f-1736-4d07-b555-07fa4d59d238
-- title:
--   Lemma 4.11 — a uniform binary matrix meets two row and two column prescriptions with probability $2^{r_xr_v}N^{-(r_x+r_v)}$ if consistent, $0$ otherwise
-- statement:
--   Let $n\ge2$ and $N=2^n$. Let $x_1,x_2$ be rows and $v_1,v_2$ columns in $\mathbb F_2^n$, with $r_x$, $r_v$ the ranks of the lists $(x_1,x_2)$ and $(v_1,v_2)$. Let $u_1,u_2$ be prescribed rows and $c_1,c_2$ prescribed columns. For $A_0$ uniform on $\mathbb F_2^{n\times n}$,
--   $$\Pr_{A_0}\big[x_iA_0=u_i\text{ and }A_0v_j=c_j\text{ for all }i,j\in\{1,2\}\big]=\begin{cases}2^{r_xr_v}N^{-(r_x+r_v)}&\text{if consistent},\\0&\text{otherwise}.\end{cases} \tag{4.46}$$
--   The prescriptions are consistent when every linear relation among the $x_i$ holds among the $u_i$, every linear relation among the $v_j$ holds among the $c_j$, and $u_i\cdot v_j=x_i\cdot c_j$ for all $i,j$.
--
--   Differences from the source:
--   - encoding: rank of the list $(x_1,x_2)$ → `Module.finrank` of the span of $\{x_1,x_2\}$; reason: the rank of a list of vectors is the dimension of its span
--   - encoding: "every linear relation among the $x_i$ holds among the $u_i$" → $\forall a,b\in\mathbb F_2,\ a x_1+b x_2=0\Rightarrow a u_1+b u_2=0$ (and likewise for $v_j,c_j$); reason: a linear relation among two vectors over $\mathbb F_2$ is a pair of coefficients
--   - encoding: $\Pr_{A_0}[\cdot]$ → the number of matrices satisfying the four equations divided by $|\mathbb F_2^{n\times n}|$; reason: uniform probability on a finite set
-- source:
--   Dziembowski, Faust, Leakage-Resilient Computation via Matrix Refreshing, arXiv:2611.04876 (sha256 fdbb2454…), p. 38, Lemma 4.11

import Mathlib
import Definitions.Def_LeakageRefresh_Continual_Encoding

namespace LeakageRefresh.Continual

open Classical in
/-- **Lemma 4.11 (Prescribed rows and columns).** For rows `x₁, x₂`, columns `v₁, v₂` with list
ranks `r_x`, `r_v`, prescribed rows `u₁, u₂`, prescribed columns `c₁, c₂`, and `A₀` uniform on
`F₂^{n×n}` (`N = 2ⁿ`):
`P[xᵢ · A₀ = uᵢ and A₀ · vⱼ = cⱼ for all i, j ∈ {1, 2}] = 2^{r_x r_v} N^{−(r_x + r_v)}` if the
prescriptions are consistent and `0` otherwise; consistent means every linear relation among the
`xᵢ` holds among the `uᵢ`, every linear relation among the `vⱼ` holds among the `cⱼ`, and
`uᵢ · vⱼ = xᵢ · cⱼ` for all `i, j`. -/
theorem lemma_4_11 (n : ℕ) (hn : 2 ≤ n) (x₁ x₂ v₁ v₂ u₁ u₂ c₁ c₂ : Fin n → ZMod 2) :
    let rx : ℕ := Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {x₁, x₂})
    let rv : ℕ := Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {v₁, v₂})
    let Consistent : Prop :=
      (∀ a b : ZMod 2, a • x₁ + b • x₂ = 0 → a • u₁ + b • u₂ = 0) ∧
      (∀ a b : ZMod 2, a • v₁ + b • v₂ = 0 → a • c₁ + b • c₂ = 0) ∧
      (u₁ ⬝ᵥ v₁ = x₁ ⬝ᵥ c₁ ∧ u₁ ⬝ᵥ v₂ = x₁ ⬝ᵥ c₂ ∧
        u₂ ⬝ᵥ v₁ = x₂ ⬝ᵥ c₁ ∧ u₂ ⬝ᵥ v₂ = x₂ ⬝ᵥ c₂)
    ((Finset.univ.filter (fun A : Matrix (Fin n) (Fin n) (ZMod 2) =>
        Matrix.vecMul x₁ A = u₁ ∧ Matrix.vecMul x₂ A = u₂ ∧
          Matrix.mulVec A v₁ = c₁ ∧ Matrix.mulVec A v₂ = c₂)).card : ℝ) /
        (Fintype.card (Matrix (Fin n) (Fin n) (ZMod 2)) : ℝ) =
      if Consistent then (2 : ℝ) ^ (rx * rv) * ((2 : ℝ) ^ n) ^ (-((rx + rv : ℕ) : ℤ)) else 0 := by sorry

end LeakageRefresh.Continual
