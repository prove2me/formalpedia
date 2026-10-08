-- Prove2me | Theorems.Thm_MaxPressure_FluidStab_xstar_mem_alloc
-- name    : MaxPressure.FluidStab.xstar_mem_alloc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:54:32.707279+00:00
-- url     : https://prove2.me/theorems/ddbce033-d5b1-4a1f-afeb-cfbe4e98e11c
-- title:
--   Proof of Theorem 5, p. 215 — x* = x̃ + x̂ ∈ 𝒜 and Rx* = Rx̂ ≥ δe with δ > 0
-- statement:
--   Let $(\tilde x,\rho)$ be a feasible solution of the static planning LP (9)–(13) with $\rho<1$. Let $\hat x\ge0$ satisfy $R\hat x>0$ and $\sum_jA_{kj}\hat x_j=0$ for every input processor $k$. Then there is a scaling factor $c>0$ such that, writing $\hat x'=c\hat x$:
--
--   1. $\sum_jA_{kj}\hat x'_j\le1-\rho$ for every service processor $k$;
--   2. $x^*=\tilde x+\hat x'$ belongs to the allocation set $\mathcal A$;
--   3. $Rx^*=R\hat x'$;
--   4. there is $\delta>0$ with $Rx^*\ge\delta e$, where $e$ is the vector of ones:
--   $$ (Rx^*)_i\ \ge\ \delta\qquad\text{for every } i\in\mathcal I .$$
--
--   In the paper $\delta=\min_i\sum_jR_{ij}\hat x'_j$. The allocation $x^*$ serves as the comparison allocation in the Lyapunov argument of Theorem 5: it is feasible and drains every buffer at rate at least $\delta$.
--
--   **Formalization Note** The constant $\delta$ is stated existentially (the minimum over an empty index set would be undefined when $I=0$); any $\delta$ with $0<\delta\le\min_i(R\hat x')_i$ serves the proof. The statement does not need the standing assumptions, which are therefore not hypotheses.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 215, proof of Theorem 5 (App. B), sentences 5–7

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Network

namespace MaxPressure.FluidStab

open Matrix

/-- Proof of Theorem 5, App. B, p. 215: let `(x̃, ρ)` be feasible for the LP (9)–(13) with
`ρ < 1`, and let `x̂ ≥ 0` satisfy `Rx̂ > 0` and `∑_j A_kj x̂_j = 0` for each input processor `k`.
Then `x̂` can be scaled (by some `c > 0`) so that `∑_j A_kj x̂_j ≤ 1 − ρ` for each service
processor `k`, and for the scaled `x̂` the allocation `x* = x̃ + x̂` lies in `𝒜`,
`Rx* = Rx̂`, and `Rx* ≥ εe` for some `ε > 0` (the paper's `δ = min_i ∑_j R_ij x̂_j`). -/
theorem xstar_mem_alloc {I J K : ℕ} (N : Network I J K)
    (xt : Fin J → ℝ) (ρ : ℝ) (hρ : ρ < 1) (hLP : LPFeasible N xt ρ)
    (xh : Fin J → ℝ) (hxh : ∀ j, 0 ≤ xh j) (hpos : ∀ i, 0 < (R N *ᵥ xh) i)
    (hin : ∀ k, N.inputProc k → ∑ j, N.A k j * xh j = 0) :
    ∃ c : ℝ, 0 < c ∧
      (∀ k, ¬ N.inputProc k → ∑ j, N.A k j * (c • xh) j ≤ 1 - ρ) ∧
      xt + c • xh ∈ allocSet N ∧
      R N *ᵥ (xt + c • xh) = R N *ᵥ (c • xh) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ (R N *ᵥ (xt + c • xh)) i := by sorry

end MaxPressure.FluidStab
