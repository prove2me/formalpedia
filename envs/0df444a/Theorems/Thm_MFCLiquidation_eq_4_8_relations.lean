-- Prove2me | Theorems.Thm_MFCLiquidation_eq_4_8_relations
-- name    : MFCLiquidation.eq_4_8_relations
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:25:25.723713+00:00
-- url     : https://prove2.me/theorems/232887c8-8b71-4a4d-930e-10989c66409f
-- title:
--   (4.8) and pp.19–20: $\mathcal K^\top A=\mathcal K^\top B=(0,-\tfrac12,0)$, $D^\top\mathcal K=0$, $I^A\mathcal K=\tilde a$, $I^B\mathcal K=a$
-- statement:
--   Let $\gamma_2>0$. For every symmetric matrix $A$ built from $(x_{11},x_{13},x_{33})$ by the relations $x_{11}=\gamma_2x_{21}$, $x_{12}=\gamma_2x_{22}+\tfrac12$, $x_{13}=\gamma_2x_{23}$, for every $D=(D_1,\gamma_2^{-1}D_1,D_3)$ and for all values of the coefficients in $I^A,I^B$:
--   $$\mathcal K^\top A=(0,-\tfrac12,0),\qquad D^\top\mathcal K=0,\qquad I^A\mathcal K=\tilde a,\qquad I^B\mathcal K=a .$$
--
--   The first identity, for both $A$ and $B$, is (4.8); these identities cancel the jump terms in the proof of Proposition 4.1 and give the initial jump in Theorem 4.2.
--
--   Differences from the source:
--   - generalization: A, B, D, I^A, I^B evaluated along the solutions of (2.14)–(2.16) → any matrix of the relation form and any values of the free entries; reason: the identities are algebraic consequences of the relations; specializing the entries to the solutions gives the paper's identities
--   - encoding: standing assumption only (γ₂ ≥ 0) → additional hypothesis 0 < γ₂; reason: every formula involved divides by γ₂ ((2.14)–(2.17), I^A, I^B, I^D, the relations A₁₂ = γ₂A₂₂ + ½); the condition only excludes parameters where the source's formulas are undefined
-- source:
--   Fu, Horst & Xia, A Mean-Field Control Problem of Optimal Portfolio Liquidation with Semimartingale Strategies, arXiv:2207.00446v3, (4.8), p.18; DᵀK = 0, p.19; "Since I^AK = ã and I^BK = a", proof of Theorem 4.2, p.20

import Mathlib
import Definitions.Def_MFCLiquidation_Params
import Definitions.Def_MFCLiquidation_Riccati

open Matrix

namespace MFCLiquidation

/-- The algebraic relations (4.8), p.18, `D^⊤𝒦 = 0`, p.19, and `I^A𝒦 = ã`, `I^B𝒦 = a`, p.20, of
arXiv:2207.00446v3. The first holds for both `A` and `B`, which are of the form `symMat`. -/
theorem eq_4_8_relations (p : Params) (hγ : 0 < p.γ₂)
    (x₁₁ x₁₃ x₃₃ d₁ d₃ a₁₁ a₁₃ b₁₁ b₁₃ b₃₃ : ℝ) :
    p.K ᵥ* p.symMat x₁₁ x₁₃ x₃₃ = ![0, -(1 / 2), 0] ∧
    p.dVec d₁ d₃ ⬝ᵥ p.K = 0 ∧
    p.IA a₁₁ a₁₃ ⬝ᵥ p.K = p.aTilde ∧
    p.IB b₁₁ b₁₃ b₃₃ ⬝ᵥ p.K = p.a := by sorry

end MFCLiquidation
