-- Prove2me | Theorems.Thm_MarkovCLTRate_eq_3_mehler_representation
-- name    : MarkovCLTRate.eq_3_mehler_representation
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:26:12.618997+00:00
-- url     : https://prove2.me/theorems/40538133-51d1-462f-ad1f-d7e16bed2e2d
-- title:
--   (3): Mehler representation of $H_k$
-- statement:
--   Let $c_t=\sqrt{1-e^{-2t}}$, $h\in Lip_1$, $V$ positive definite, $V'$ positive semidefinite and $a\in\Re^d$. Let $A(a)$ be the matrix $A_{k,h}$ of Theorem 1 built from $Q=V^{1/2}$ and $\Lambda=V^{-1/2}V'V^{-1/2}$ at the shift $a$. Then
--   $$
--   V^{-1/2}A(a)V^{-1/2}=-\int_0^\infty e^{-2t}\,E_{\xi\sim N(0,V')}\big[\nabla^2P_{c_t^2V}h(a+e^{-t}\xi)\big]\,dt .
--   $$
--   With $V=V_k$, $V'=V_{k+1}$ and $a=S_{k-1}$ this is the representation (3) of $H_k=V_k^{-1/2}A_{k,h}(\mathcal F_{k-1})V_k^{-1/2}$.
--
--   It reduces the comparison of $H_k$ and $H_{k-1}$ to Gaussian-smoothing estimates for $h$.
--
--   **Formalization Note** Both sides are compared entry by entry; the outer integral is over $t\in(0,\infty)$.
--
--   Differences from the source:
--   - generalization: V_k, V_{k+1}, S_{k−1} of the chain (stationary finite chain in Lemma 3; general chain on p.21) → any positive definite V, positive semidefinite V' and deterministic shift a; reason: the identity concerns fixed matrices and a fixed shift; conditional on 𝓕_{k−1} the shift S_{k−1} is fixed, so it specializes to (3)
--   - encoding: c_t² V → (1 − e^{−2t}) • V; reason: c_t² = 1 − e^{−2t}
-- source:
--   Srikant, Rates of Convergence in the Central Limit Theorem for Markov Chains, with an Application to TD Learning, arXiv:2401.15719v5, proof of Lemma 3, (3), p.11

import Mathlib
import Definitions.Def_MarkovCLTRate_Basic
import Definitions.Def_MarkovCLTRate_Stein

open MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder

namespace MarkovCLTRate

/-- **The Mehler representation (3)**, arXiv:2401.15719v5, proof of Lemma 3, p.11. With
`c_t = √(1 − e^{−2t})`, `H_k = V_k^{−1/2} A_{k,h} V_k^{−1/2}` satisfies
`H_k = −∫_0^∞ e^{−2t} E_{ξ∼N(0,V_{k+1})}[∇²P_{c_t² V_k} h(S_{k−1} + e^{−t}ξ)] dt`   (3).

Here it is stated for a deterministic shift `a` in place of `S_{k−1}`, a positive definite `V` in
place of `V_k` and a positive semidefinite `V'` in place of `V_{k+1}`, for every `h ∈ Lip_1`:
`V^{−1/2} A(a) V^{−1/2} = −∫_0^∞ e^{−2t} ∫ ∇²P_{c_t² V} h(a + e^{−t}ξ) dN(0, V')(ξ) dt`,
where `A(a)` is the matrix `A_{k,h}` of Theorem 1 built from `Q = V^{1/2}` and
`Λ = V^{−1/2} V' V^{−1/2}`.

**Formalization Note.** Both sides are compared entrywise; the outer integral is over `t ∈ (0, ∞)`.
Conditional on `𝓕_{k−1}` the shift `S_{k−1}` is fixed, so the identity for every `a` gives (3).
The page uses it with `V = V_k`, `V' = V_{k+1}`; no ordering between `V` and `V'` is needed. -/
theorem eq_3_mehler_representation {d : ℕ} (V V' : Mat d) (hV : V.PosDef)
    (hV' : V'.PosSemidef) (h : Vec d → ℝ) (hh : LipschitzWith 1 h) (a : Vec d) (i j : Fin d) :
    (minvSqrt V * steinA h (msqrt V) (minvSqrt V * V' * minvSqrt V) a * minvSqrt V) i j
      = -∫ t in Set.Ioi (0 : ℝ), Real.exp (-2 * t) *
          ∫ ξ, hessMat (gaussSmooth ((1 - Real.exp (-2 * t)) • V) h) (a + Real.exp (-t) • ξ) i j
            ∂(multivariateGaussian 0 V') := by sorry

end MarkovCLTRate
