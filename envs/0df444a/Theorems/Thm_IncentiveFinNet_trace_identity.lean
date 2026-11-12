-- Prove2me | Theorems.Thm_IncentiveFinNet_trace_identity
-- name    : IncentiveFinNet.trace_identity
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:18:18.321651+00:00
-- url     : https://prove2.me/theorems/41d3c63a-0b96-4398-ac84-e0c0304b4949
-- title:
--   A.1, trace identity: the right side of (6) equals $\mathrm{uvec}(R)^{\top}\mathrm{uvec}(C_{(i,j)})$
-- statement:
--   Let $Q_1,\dots,Q_n$ be symmetric $n\times n$ real matrices and let $B_{(i,j)} = e_ie_j^{\top}Q_i$ and $C_{(i,j)} = (B_{(i,j)} - B_{(j,i)}) - (B_{(i,j)} - B_{(j,i)})^{\top}$. Let $R$ be an $n \times n$ upper-triangular matrix with zero diagonal and $P = R - R^{\top}$. Then for all $i, j \in [n]$,
--   $$
--   \begin{aligned}
--   e_i^{\top}\bigl(Q_jP - (Q_iP)^{\top}\bigr)e_j &= e_i^{\top}(Q_jP + PQ_i)e_j \\
--   &= \operatorname{tr} P\bigl(e_je_i^{\top}Q_j + Q_ie_je_i^{\top}\bigr) \\
--   &= \operatorname{tr}(R - R^{\top})\bigl(B_{(j,i)} + B_{(i,j)}^{\top}\bigr) \\
--   &= \operatorname{tr} R^{\top}C_{(i,j)} \\
--   &= \mathrm{uvec}(R)^{\top}\mathrm{uvec}(C_{(i,j)}),
--   \end{aligned}
--   $$
--   where $\mathrm{uvec}$ lists the entries strictly above the diagonal, so the last term is $\sum_{k<l} R_{kl}\,(C_{(i,j)})_{kl}$.
--
--   Applied to the network setting's matrices $Q_i$, this turns condition (6) of the proof of Theorem 1 into a linear equation in the upper-triangular entries of the price matrix, whose coefficient vector is $\mathrm{uvec}(C_{(i,j)})$.
--
--   Differences from the source:
--   - generalization: Q_i the network setting's matrices Ψ_iᵀ(2γ_iΨ_iΣ_iΨ_iᵀ)⁻¹Ψ_i, which satisfy Q_i = Q_iᵀ → an arbitrary family of symmetric matrices Q_i; reason: the computation uses only Q_i = Q_iᵀ, and the setting's Q_i are symmetric, so the source's case is a special case
--   - encoding: Since P = −Pᵀ, we must have P = R − Rᵀ with R upper-triangular with zero diagonal → R with R_kl = 0 unless k < l, and P = R − Rᵀ, as hypotheses; reason: the same pair (R, P); every skew-symmetric P arises this way
--   - encoding: uvec(R)ᵀuvec(C_(i,j)) → the sum of R_kl·(C_(i,j))_kl over all pairs k < l; reason: the definition of uvec
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, A.1 (Proof of Theorem 1), trace identity following (6), pp.33–34

import Mathlib
import Definitions.Def_IncentiveFinNet_matC

open Matrix

namespace IncentiveFinNet

/-- **A.1, trace identity**, Jalan, Chakrabarti, Sarkar, arXiv:2212.06808v3, pp.33–34: with
`P = R − Rᵀ`, `R` upper-triangular with zero diagonal, and `Q_i = Q_iᵀ`,
`e_iᵀ(Q_j P − (Q_i P)ᵀ)e_j = e_iᵀ(Q_j P + P Q_i)e_j = tr P(e_j e_iᵀ Q_j + Q_i e_j e_iᵀ)
= tr(R − Rᵀ)(B_{(j,i)} + B_{(i,j)}ᵀ) = tr Rᵀ C_{(i,j)} = uvec(R)ᵀ uvec(C_{(i,j)})`.

All five equalities of the chain are stated.

**Formalization Note** Stated for an arbitrary family of symmetric matrices `Q_i` (the identity
uses only `Q_i = Q_iᵀ`); `B`, `C` are `matB Q`, `matC Q`; `e_j e_iᵀ` is
`vecMulVec (Pi.single j 1) (Pi.single i 1)`. `uvec(R)ᵀ uvec(C)` is the sum of `R_kl C_kl` over
all pairs `k < l`. -/
theorem trace_identity {n : ℕ} (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ i, (Q i)ᵀ = Q i) (R P : Matrix (Fin n) (Fin n) ℝ) (hR : ∀ k l, ¬ k < l → R k l = 0) (hP : P = R - Rᵀ) (i j : Fin n) : (Q j * P - (Q i * P)ᵀ) i j = (Q j * P + P * Q i) i j ∧ (Q j * P + P * Q i) i j = (P * (vecMulVec (Pi.single j 1) (Pi.single i 1) * Q j + Q i * vecMulVec (Pi.single j 1) (Pi.single i 1))).trace ∧ (P * (vecMulVec (Pi.single j 1) (Pi.single i 1) * Q j + Q i * vecMulVec (Pi.single j 1) (Pi.single i 1))).trace = ((R - Rᵀ) * (matB Q j i + (matB Q i j)ᵀ)).trace ∧ ((R - Rᵀ) * (matB Q j i + (matB Q i j)ᵀ)).trace = (Rᵀ * matC Q i j).trace ∧ (Rᵀ * matC Q i j).trace = ∑ k, ∑ l, if k < l then R k l * matC Q i j k l else 0 := by sorry

end IncentiveFinNet
