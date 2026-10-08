-- Prove2me | Theorems.Thm_MFGPlanning_Penalized_theorem_2
-- name    : MFGPlanning.Penalized.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T20:19:01.846383+00:00
-- url     : https://prove2.me/theorems/1e719c84-aba5-42a4-a202-fe0c40855e77
-- title:
--   Theorem 2 — the penalized problem (50) has a minimizer, and its optimality system is the penalized scheme (20)–(23)
-- statement:
--   Assume the hypotheses of Theorem 1: $g$ satisfies (G1), (G3), (G4), (G5); $W$ satisfies (24); $m_0, m_T \in \mathcal K$ with $(m_0)_{i,j} > 0$ for all $(i,j)$; and either $\nu > 0$, or $\nu = 0$ and $(m_T)_{i,j} > 0$ for all $(i,j)$. Let $\varepsilon > 0$. Then the minimization problem
--   $$
--   \text{Minimize } \Theta^*(M, Z) + \frac{1}{2\varepsilon\Delta t}\sum_{i,j}\big(M^0_{i,j} - (m_0)_{i,j}\big)^2
--   $$
--   subject to
--   $$
--   \frac{M^{n+1}_{i,j} - M^n_{i,j}}{\Delta t} + \nu(\Delta_hM^n)_{i,j} + \mathrm{div}_h(Z^n)_{i,j} = 0 \quad (0 \le n < N_T), \qquad M^{N_T}_{i,j} = (m_T)_{i,j}, \tag{50}
--   $$
--   where $\Theta^*$ is given by (25), has a solution $(M^\varepsilon, Z^\varepsilon)$. Moreover there is a family of grid functions $U^\varepsilon$ with
--   $$
--   Z^{\varepsilon,k,n}_{i,j} = M^{\varepsilon,n}_{i,j}\,\frac{\partial g}{\partial q_k}\big(x_{i,j}, [D_hU^{\varepsilon,n+1}]_{i,j}\big),
--   $$
--   and the pair $(U^\varepsilon, M^\varepsilon)$ solves the penalized discrete system (20)–(23).
--
--   This is the optimal-control interpretation of the penalized scheme; it is what Proposition 2 compares against a solution of the planning scheme.
--
--   **Formalization Note** $\Theta^*$ acts on the levels $0, \dots, N_T - 1$ of $M$, as in (25). The objective is valued in $(-\infty, +\infty]$, and minimality is stated against every admissible pair. The paper says "there exists a solution $U^\varepsilon$ of the dual problem (which we do not write)"; since that problem is not written, the statement asserts the existence of $U^\varepsilon$ with the two displayed properties. "The solution of (20)–(23)" is stated as "a solution". Indices $k = 1, \dots, 4$ are `0, 1, 2, 3` in Lean. (G2) is not encoded.
-- source:
--   Achdou, Camilli, Capuzzo-Dolcetta, Mean field games: numerical methods for the planning problem, hal-00465404v1 (2010), §3.2, Theorem 2, eq. (50), p. 14

import Mathlib
import Definitions.Def_MFGPlanning_Penalized_Grid
import Definitions.Def_MFGPlanning_Penalized_Hyp
import Definitions.Def_MFGPlanning_Penalized_Scheme
import Definitions.Def_MFGPlanning_Penalized_Duality

namespace MFGPlanning.Penalized

/-- Theorem 2, hal-00465404v1, §3.2, p. 14 (PDF 15). Under the assumptions of Theorem 1 and
for ε > 0, the problem (50)
  minimize Θ*(M, Z) + (1/(2εΔt)) Σ_{i,j} (M^0_{i,j} − (m_0)_{i,j})²
  subject to (M^{n+1} − M^n)/Δt + ν Δ_hM^n + div_h(Z^n) = 0 (0 ≤ n < N_T), M^{N_T} = m_T
has a solution (M^ε, Z^ε), and there is U^ε with Z^{ε,k,n} = M^{ε,n} ∂g/∂q_k(x, [D_hU^{ε,n+1}])
such that (U^ε, M^ε) solves the penalized scheme (20)–(23).
Formalization Note: Θ* acts on the levels 0, …, N_T − 1 of M (`Fin.init M`), as in (25)
and Remark 2; the objective is `EReal`-valued (Θ* may be +∞) and the penalty is a real number
added to it. "A solution U^ε of the dual problem (which we do not write)" is rendered as the
existence of U^ε with the two displayed properties; "the solution" of (20)–(23) as "a solution".
Z^k, q_k for k = 1, …, 4 are the indices `0, 1, 2, 3` of `Fin 4`. (G₂) is not encoded. -/
theorem theorem_2 (d : Data) (hG1 : G1 d) (hG3 : G3 d) (hG4 : G4 d) (hG5 : G5 d) (hW : HypW d)
    (hm0 : InK d d.m0) (hmT : InK d d.mT) (hm0pos : ∀ p, 0 < d.m0 p)
    (hνmT : 0 < d.ν ∨ (d.ν = 0 ∧ ∀ p, 0 < d.mT p))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (M : Fin (d.NT + 1) → Pt d → ℝ) (Z : Fin d.NT → Pt d → Fin 4 → ℝ),
      ((∀ (n : Fin d.NT) (p : Pt d),
          (M n.succ p - M n.castSucc p) / d.Δt + d.ν * lap d (M n.castSucc) p
            + divh d (Z n) p = 0) ∧ M (Fin.last d.NT) = d.mT) ∧
      (∀ (M' : Fin (d.NT + 1) → Pt d → ℝ) (Z' : Fin d.NT → Pt d → Fin 4 → ℝ),
        ((∀ (n : Fin d.NT) (p : Pt d),
            (M' n.succ p - M' n.castSucc p) / d.Δt + d.ν * lap d (M' n.castSucc) p
              + divh d (Z' n) p = 0) ∧ M' (Fin.last d.NT) = d.mT) →
        ΘStar d (Fin.init M) Z
            + (((1 / (2 * ε * d.Δt)) * ∑ p, (M 0 p - d.m0 p) ^ 2 : ℝ) : EReal)
          ≤ ΘStar d (Fin.init M') Z'
            + (((1 / (2 * ε * d.Δt)) * ∑ p, (M' 0 p - d.m0 p) ^ 2 : ℝ) : EReal)) ∧
      ∃ U : Fin (d.NT + 1) → Pt d → ℝ,
        (∀ (k : Fin d.NT) (p : Pt d) (l : Fin 4),
          Z k p l = M k.castSucc p * dg d p (Dh d (U k.succ) p) l) ∧
        IsPenalizedSol d ε U M := by sorry

end MFGPlanning.Penalized
