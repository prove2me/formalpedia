-- Prove2me | Theorems.Thm_MFGPlanning_Existence_theorem_1
-- name    : MFGPlanning.Existence.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T20:01:36.354472+00:00
-- url     : https://prove2.me/theorems/c3a94fef-5a32-47fb-943c-7ad18c7a1818
-- title:
--   Theorem 1 — the saddle point problem (31) has a solution, and it solves the discrete planning scheme (18)
-- statement:
--   Assume that
--
--   1. $g$ satisfies (G1), (G3), (G4), (G5);
--   2. $W$ satisfies (24), with $V = W'$;
--   3. $m_0, m_T\in\mathcal K$, with $(m_0)_{i,j} > 0$ for all $i,j$;
--   4. either $\nu > 0$, or $\nu = 0$ and $(m_T)_{i,j} > 0$ for all $i,j$.
--
--   Then the saddle point problem
--   $$\min_{M,Z}\ \Theta^*(M,Z) + \Sigma^*(-M,-Z) = -\min_{\alpha,\beta}\big(\Theta(\alpha,\beta) + \Sigma(\alpha,\beta)\big) \tag{31}$$
--   has a solution: there are $(M,Z)$ minimizing the left-hand side and $(\alpha,\beta)$ minimizing the right-hand side, the two optimal values are finite and satisfy (31). Moreover, there is $U = (U^n)_{0\le n\le N_T}$ with $\sum_{i,j}U^0_{i,j} = 0$ and $(\alpha,\beta) = \Lambda(U)$, such that the optimality conditions of (31) hold; these are equivalent to the discrete system (18): $(U, M)$, with $M^{N_T} := m_T$ appended, solves the fully discrete planning scheme (18), and
--   $$Z^{k,n}_{i,j} = M^n_{i,j}\,\frac{\partial g}{\partial q_k}\big(x_{i,j},[D_hU^{n+1}]_{i,j}\big),\qquad k = 1,\dots,4,\ 0\le n<N_T. \tag{39}$$
--
--   This is the existence theorem for the finite-difference planning problem: a discrete mean field game with prescribed initial and final densities has a solution, obtained as the saddle point of a pair of convex problems in duality.
--
--   **Formalization Note** (G2) is not a hypothesis: it only links $g$ to the continuous Hamiltonian $H$. The optimality conditions (32)–(33), $-\Lambda^*(M,Z)\in\partial\mathcal F(U)$ and $\Lambda(U)\in\partial\Theta^*(M,Z)$, are stated through what the theorem says they are equivalent to, namely the scheme (18) together with the relation (39) between $Z$ and $M\nabla_q g$ derived from (33) in the proof. The finiteness of the common value and $\sum_{i,j}U^0_{i,j} = 0$ (which follows from $\Sigma(\alpha,\beta) < +\infty$ and (29)) are added, true and stronger, clauses. All functionals are `EReal`-valued. Time indices: `M k`, `Z k` are $M^k$, $Z^k$ ($0\le k<N_T$), `α k`, `β k` are $\alpha^{k+1}$, $\beta^{k+1}$, and $U$ has levels $0,\dots,N_T$.
-- source:
--   Achdou, Camilli, Capuzzo-Dolcetta, Mean field games: numerical methods for the planning problem, hal-00465404v1 (2010), Theorem 1, p. 10 (with (39), p. 11)

import Mathlib
import Definitions.Def_MFGPlanning_Existence_Grid
import Definitions.Def_MFGPlanning_Existence_Hyp
import Definitions.Def_MFGPlanning_Existence_Scheme
import Definitions.Def_MFGPlanning_Existence_Duality

namespace MFGPlanning.Existence

/-- Theorem 1 of Achdou, Camilli, Capuzzo-Dolcetta, hal-00465404v1 (2010), §3.1, p. 10 (PDF 11):
under (G1)–(G5), (24), `m_0, m_T ∈ 𝒦`, `m_0 > 0`, and `ν > 0` or (`ν = 0` and `m_T > 0`), the saddle
point problem (31) `min_{M,Z} Θ^*(M, Z) + Σ^*(−M, −Z) = − min_{α,β} (Θ(α, β) + Σ(α, β))` has a solution
`(M, Z)`, `(α, β)`, there is `U` with `(α, β) = Λ(U)`, and the optimality conditions (32)–(33) hold,
which are equivalent to the discrete system (18).

Formalization Note: (G2) is not a hypothesis (it only defines the continuous Hamiltonian `H`). The
optimality conditions (32)–(33) are stated through what the theorem says they are equivalent to:
`(U, M)` with `M^{N_T} = m_T` appended solves (18), together with the relation (39)
`Z^{k,n} = M^n ∂g/∂q_k(x, [D_h U^{n+1}])` derived from (33). Added (true, stronger) clauses: the common
value of (31) is finite, and `∑_{i,j} U^0_{i,j} = 0`. -/
theorem theorem_1 (d : Data) (hG1 : G1 d) (hG3 : G3 d) (hG4 : G4 d) (hG5 : G5 d) (hW : A24 d)
    (hm0 : InK d d.m0) (hmT : InK d d.mT) (hm0pos : ∀ p, 0 < d.m0 p)
    (hν : 0 < d.ν ∨ (d.ν = 0 ∧ ∀ p, 0 < d.mT p)) :
    ∃ (M : Fin d.NT → d.Pt → ℝ) (Z : Fin d.NT → d.Pt → Fin 4 → ℝ)
      (α : Fin d.NT → d.Pt → ℝ) (β : Fin d.NT → d.Pt → Fin 4 → ℝ)
      (U : Fin (d.NT + 1) → d.Pt → ℝ),
      (∀ (M' : Fin d.NT → d.Pt → ℝ) (Z' : Fin d.NT → d.Pt → Fin 4 → ℝ),
        ThetaStar d M Z + SigmaStar d (-M) (-Z) ≤ ThetaStar d M' Z' + SigmaStar d (-M') (-Z')) ∧
      (∀ (α' : Fin d.NT → d.Pt → ℝ) (β' : Fin d.NT → d.Pt → Fin 4 → ℝ),
        Theta d α β + SigmaF d α β ≤ Theta d α' β' + SigmaF d α' β') ∧
      ThetaStar d M Z + SigmaStar d (-M) (-Z) = -(Theta d α β + SigmaF d α β) ∧
      ThetaStar d M Z + SigmaStar d (-M) (-Z) ≠ ⊤ ∧
      ThetaStar d M Z + SigmaStar d (-M) (-Z) ≠ ⊥ ∧
      Lam d U = (α, β) ∧ ∑ p, U 0 p = 0 ∧
      IsPlanningSol d U (Fin.snoc (α := fun _ => d.Pt → ℝ) M d.mT) ∧
      ∀ (k : Fin d.NT) (p : d.Pt) (l : Fin 4), Z k p l = M k p * dg d p (Dh d (U k.succ) p) l := by sorry

end MFGPlanning.Existence
