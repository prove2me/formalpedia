-- Prove2me | Theorems.Thm_GaoQuantumUnion_coding_application
-- name    : GaoQuantumUnion.coding_application
-- status  : Open
-- author  : @Mrnaiq
-- created : 2026-11-19T21:47:16.308866+00:00
-- url     : https://prove2.me/theorems/95c74e2d-8357-4226-9500-64336553ece7
-- title:
--   Sequential decoding — Finite independent-codebook error estimate
-- statement:
--   Let $p_j,\rho_j$ be a finite ensemble, $P,Q_j$ orthogonal projectors, and $\bar\rho=\sum_jp_j\rho_j$. Assume $\operatorname{Tr}(P\bar\rho)\ge1-\varepsilon$, $\operatorname{Tr}(Q_j\rho_j)\ge1-\varepsilon$, $\operatorname{Tr}Q_j\le B$, and $P\bar\rho P\preceq AI$, with $\varepsilon>0$ and $A,B\ge0$. For $M>0$, independently sample $M$ codewords from $p$, and decode in sequence using the actual projector experiment. Then
--
--   $$\mathbb E_C e(C)\le33\varepsilon+4(M-1)AB,$$
--
--   and a codebook exists with average error bounded by the same expression. This is the algebraic finite form of the paper's estimates before substituting $A=2^{-n(S(\bar\rho)-\delta)}$ and $B=2^{n(\sum_jp_jS(\rho_j)+\delta)}$. The expectation is the explicit product-weight sum over all codebooks, with repetitions allowed; the required estimates are conclusions, not additional assumptions.
-- source:
--   Jingliang Gao, Quantum union bounds for sequential projective measurements, arXiv:1410.5688v2, Physical Review A 92, 052331 (2015), https://doi.org/10.1103/PhysRevA.92.052331; PDF pp. 10–12, hypotheses (17)–(20) and the expectation estimates culminating in the coding-error bound

import Definitions.Def_GaoQuantumUnion_Decoding
open Matrix WildeQIT GaoQuantumUnion
open scoped MatrixOrder ComplexOrder ComplexConjugate
set_option autoImplicit false

namespace GaoQuantumUnion
theorem coding_application {ι J : Type} [Fintype ι] [DecidableEq ι]
    [Fintype J] [DecidableEq J] (p : FinDist J) (ρ : J → Matrix ι ι ℂ)
    (hρ : ∀ j, IsDensityOperator (ρ j)) (P : Matrix ι ι ℂ) (hP : IsProjector P)
    (Q : J → Matrix ι ι ℂ) (hQ : ∀ j, IsProjector (Q j))
    (ε A B : ℝ) (hε : 0 < ε) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (havg : 1-ε ≤ (P*WildeQIT.Gentle.averageState p ρ).trace.re)
    (hdetect : ∀ j, 1-ε ≤ (Q j*ρ j).trace.re)
    (hsize : ∀ j, (Q j).trace.re ≤ B)
    (hsandwich : ((A : ℂ) • (1 : Matrix ι ι ℂ)-P*WildeQIT.Gentle.averageState p ρ*P).PosSemidef)
    (M : ℕ) (hM : 0 < M) :
    (∑ C : Fin M → J, codeWeight p C*codeError ρ P Q C) ≤ 33*ε+4*((M : ℝ)-1)*A*B ∧
    ∃ C : Fin M → J, codeError ρ P Q C ≤ 33*ε+4*((M : ℝ)-1)*A*B := by sorry
end GaoQuantumUnion
