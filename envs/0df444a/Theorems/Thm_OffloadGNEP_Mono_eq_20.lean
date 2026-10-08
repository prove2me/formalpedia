-- Prove2me | Theorems.Thm_OffloadGNEP_Mono_eq_20
-- name    : OffloadGNEP.Mono.eq_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:48.85308+00:00
-- url     : https://prove2.me/theorems/a8094a78-de37-410d-87b8-cd14ef9db61d
-- title:
--   (20), p. 13 — Bˢ = (1/(nD²)) δδᵀ ∘ (I + E + (1/(nD))(x^δ_clet eᵀ + e(x^δ_clet)ᵀ))
-- statement:
--   Assume Assumption A and the standing hypotheses, and let $x\in\mathbb R^{3N}$ with $D=1-\frac1n\sum_t\delta_tx_{t,clet}\ne0$. Write $\delta=(\delta_1,\dots,\delta_N)^\top$, $x^\delta_{clet}=(\delta_1x_{1,clet},\dots,\delta_Nx_{N,clet})^\top$, $e$ for the all-ones vector of $\mathbb R^N$, $E$ for the all-ones $N\times N$ matrix, $I$ for the identity and $\circ$ for the Hadamard (entrywise) product. Then the symmetric part $B^s=\frac12(B^\top+B)$ of the clet-block of the Jacobian is
--   $$B^s=\frac1{nD^2}\Big(\delta\delta^\top\circ\Big(I+E+\frac1{nD}\big(x^\delta_{clet}e^\top+e(x^\delta_{clet})^\top\big)\Big)\Big).$$
--
--   This factorisation exhibits $B^s$ as a Hadamard product with the positive semidefinite matrix $\delta\delta^\top$, which is what makes the Schur product theorem applicable.
--
--   **Formalization Note** The only hypothesis the identity needs beyond the definitions is $D\neq0$, so that the denominators of $B_u$, $B_{uv}$ are not Lean's junk value.
-- source:
--   Cardellini et al., A game-theoretic approach to computation offloading in mobile cloud computing, accepted manuscript (IRIS Sapienza 11573/779661; DOI 10.1007/s10107-015-0881-6), pp. 12–13, definition of D and (20)

import Mathlib
import Definitions.Def_OffloadGNEP_Mono_Setting

namespace OffloadGNEP.Mono

theorem eq_20 {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
    (x : Fin N → Tier → ℝ) (hD : D P x ≠ 0) :
    Bs P x = (1 / ((P.n : ℝ) * D P x ^ 2)) •
      (Matrix.vecMulVec P.delta P.delta).hadamard
        (1 + Eall + (1 / ((P.n : ℝ) * D P x)) •
          (Matrix.vecMulVec (xdelta P x) ones + Matrix.vecMulVec ones (xdelta P x))) := by sorry

end OffloadGNEP.Mono
