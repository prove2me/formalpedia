-- Prove2me | Theorems.Thm_MFGPlanning_Existence_positivity
-- name    : MFGPlanning.Existence.positivity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T20:00:10.701657+00:00
-- url     : https://prove2.me/theorems/6c13ff26-49db-4b78-9945-40fb945dd531
-- title:
--   Proof of Theorem 1, pp. 11–12 — discrete strong maximum principle: $M^n > 0$ for $n < N_T$
-- statement:
--   Assume (G1) and (G3), and either $\nu > 0$, or $\nu = 0$ and $(m_T)_{i,j} > 0$ for all $i,j$. Let $U = (U^n)$ and $M = (M^n)$, $n = 0,\dots,N_T$, be grid functions with $M^n \in\mathcal K$ for every $n$, $M^{N_T} = m_T$, and
--   $$\frac{M^{n+1}_{i,j}-M^n_{i,j}}{\Delta t} + \nu(\Delta_hM^n)_{i,j} + \mathcal B_{i,j}(U^{n+1},M^n) = 0,\qquad 0\le n<N_T,\ \text{all } i,j. \tag{42}$$
--   Then
--   $$M^n_{i,j} > 0\qquad\text{for all } 0\le n<N_T \text{ and all } i,j.$$
--
--   In the proof of Theorem 1 this turns the complementarity conditions (41), which hold with an inequality where $M^n_{i,j} = 0$, into the equality (43), i.e. into the Hamilton–Jacobi line of the scheme (18).
--
--   **Formalization Note** No hypothesis on $W$ and only (G1), (G3) on $g$ are assumed. Time level $n$ is `n : Fin (NT+1)`; the levels $0\le n<N_T$ are `n.castSucc`.
-- source:
--   Achdou, Camilli, Capuzzo-Dolcetta, Mean field games: numerical methods for the planning problem, hal-00465404v1 (2010), §3.1, proof of Theorem 1, pp. 11–12, from "Finally, let us prove" to "in contradiction with the hypothesis."; (42), p. 11

import Mathlib
import Definitions.Def_MFGPlanning_Existence_Grid
import Definitions.Def_MFGPlanning_Existence_Hyp

namespace MFGPlanning.Existence

/-- Positivity step of the proof of Theorem 1, Achdou, Camilli, Capuzzo-Dolcetta, hal-00465404v1
(2010), §3.1, pp. 11–12 (PDF 12–13), "Finally, let us prove that `M^n > 0` for all `0 ≤ n < N_T`":
if `M^n ∈ 𝒦` for all `n`, `M^{N_T} = m_T`, and `(U, M)` satisfies the discrete Fokker–Planck
equation (42) for `0 ≤ n < N_T`, and either `ν > 0` or (`ν = 0` and `m_T > 0`), then `M^n > 0` for
`0 ≤ n < N_T`.

Formalization Note: only (G1) and (G3) are assumed on `g`, nothing on `W`. Time level `n` is
`n : Fin (N_T + 1)`; the levels `0 ≤ n < N_T` are `n.castSucc` for `n : Fin N_T`. -/
theorem positivity (d : Data) (hG1 : G1 d) (hG3 : G3 d)
    (hν : 0 < d.ν ∨ (d.ν = 0 ∧ ∀ p, 0 < d.mT p))
    (U M : Fin (d.NT + 1) → d.Pt → ℝ) (hK : ∀ n, InK d (M n))
    (hT : M (Fin.last d.NT) = d.mT)
    (h42 : ∀ (n : Fin d.NT) (p : d.Pt),
      (M n.succ p - M n.castSucc p) / d.dt + d.ν * lap d (M n.castSucc) p
        + B d (U n.succ) (M n.castSucc) p = 0) :
    ∀ (n : Fin d.NT) (p : d.Pt), 0 < M n.castSucc p := by sorry

end MFGPlanning.Existence
