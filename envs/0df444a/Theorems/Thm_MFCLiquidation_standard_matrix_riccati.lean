-- Prove2me | Theorems.Thm_MFCLiquidation_standard_matrix_riccati
-- name    : MFCLiquidation.standard_matrix_riccati
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:25:46.897645+00:00
-- url     : https://prove2.me/theorems/e0d73fda-33e0-4839-9604-c6cdfb00cb2e
-- title:
--   Standard matrix Riccati equation: unique global positive semidefinite solution (cited [47, Prop. 2.1, 2.2], p.15)
-- statement:
--   Let $n\in\mathbb N$ and let $S,N,Q,G$ be real $n\times n$ matrices with $S$, $Q$ and $G$ symmetric positive semidefinite, and let $T>0$. Then the backward matrix Riccati equation
--   $$\dot P_t=P_tSP_t+NP_t+P_tN^\top-Q,\qquad t\in[0,T],\qquad P_T=G,$$
--   has a solution on $[0,T]$, every $P_t$ is symmetric positive semidefinite, and any two solutions agree on $[0,T]$.
--
--   This is the deterministic, constant-coefficient case of Kohlmann and Tang's result, which the paper applies to (3.2) with $S=\mathcal N_2\mathcal N_0\mathcal N_2^\top$ (rank one, so only semidefinite), $N=\tilde{\mathcal N}_1$, $Q=\tilde{\mathcal M}$ and $G=\tilde{\mathcal P}_T$.
--
--   Differences from the source:
--   - generalization: (3.2): 2 × 2 symmetric matrices, the specific S, Ñ₁, M̃, terminal value → any n, any S, Q, G symmetric positive semidefinite and any N; solution unique among all matrix-valued functions and positive semidefinite; reason: the paper's instance is n = 2 with S = 𝒩₂𝒩₀𝒩₂ᵀ ⪰ 0, Q = ℳ̃ ⪰ 0 and G = G + Λ̃ ≻ 0 (milestone mTilde_posSemidef), so the Lean statement specializes to the paper's claim about (3.2)
--   - encoding: a solution of the backward ODE on [0, T] (in L^∞ ∩ C([0, T])) → functions ℝ → ℝ with derivative within [0, T] (one-sided at the endpoints) equal to the right side at every point of [0, T], plus the terminal values; reason: a continuous solution of the integrated equation is C¹ on [0, T], so the two classes coincide; values outside [0, T] play no role
-- source:
--   Fu, Horst & Xia, A Mean-Field Control Problem of Optimal Portfolio Liquidation with Semimartingale Strategies, arXiv:2207.00446v3, p.15: "all the coefficients in (3.2) satisfy the requirements in [47, Proposition 2.1, 2.2]. As a result, the system (3.2) has a unique solution in L∞([0, T]; S²) ∩ C([0, T]; S²)." ([47] Kohlmann–Tang, deterministic constant-coefficient case)

import Mathlib
import Definitions.Def_MFCLiquidation_Params
import Definitions.Def_MFCLiquidation_Riccati

open Set

namespace MFCLiquidation

/-- The standard matrix Riccati equation, in the deterministic constant-coefficient case of
Kohlmann–Tang [47, Propositions 2.1, 2.2], as used on p.15 of arXiv:2207.00446v3: if `S`, `Q` and
the terminal matrix `G` are symmetric positive semidefinite, then `Ṗ = PSP + NP + PNᵀ − Q`,
`P_T = G`, has a unique solution on `[0, T]`, and it is symmetric positive semidefinite. -/
theorem standard_matrix_riccati {n : ℕ} (S N Q G : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.PosSemidef) (hQ : Q.PosSemidef) (hG : G.PosSemidef) (T : ℝ) (hT : 0 < T) :
    ∃ P : ℝ → Matrix (Fin n) (Fin n) ℝ, IsMatRiccati S N Q G T P ∧
      (∀ s ∈ Icc 0 T, (P s).PosSemidef) ∧
      ∀ P' : ℝ → Matrix (Fin n) (Fin n) ℝ, IsMatRiccati S N Q G T P' →
        ∀ s ∈ Icc 0 T, P' s = P s := by sorry

end MFCLiquidation
