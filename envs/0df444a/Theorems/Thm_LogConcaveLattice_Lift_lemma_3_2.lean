-- Prove2me | Theorems.Thm_LogConcaveLattice_Lift_lemma_3_2
-- name    : LogConcaveLattice.Lift.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:01:39.25886+00:00
-- url     : https://prove2.me/theorems/c574a9a3-a79a-42c1-ad11-a59d0ebb6716
-- title:
--   Lemma 3.2 — $0\preccurlyeq\operatorname{Cov}(D_{\Lambda,A})\preccurlyeq\operatorname{Cov}(D_{x+\Lambda,A})$
-- statement:
--   Let $\Lambda\subseteq\mathbb R^n$ be a full-rank lattice, let $x\in\mathbb R^n$ and let $A$ be a symmetric positive-definite matrix. Then the covariance of the discrete Gaussian $D_{x+\Lambda,A}$ (the law on $x+\Lambda$ with $\mathbb P(Y=y)=\rho_A(y)/\rho_A(x+\Lambda)$, $\rho_A(y)=e^{-\pi\langle y,A^{-1}y\rangle}$) is minimized at $x=0$:
--   $$0\preccurlyeq\operatorname{Cov}(D_{\Lambda,A})\preccurlyeq\operatorname{Cov}(D_{x+\Lambda,A}),$$
--   in the Loewner order $S\preccurlyeq T\iff\langle v,Sv\rangle\le\langle v,Tv\rangle$ for all $v$.
--
--   This comparison lets the proof of Theorem 1.1 bound the Hessian of $-\log f$ at every point by its value at the origin.
--
--   Differences from the source:
--   - encoding: ρ_A(x) = exp(−π⟨x, A⁻¹x⟩) → the mission's ρ_A defined through the pseudoinverse; Cov as the matrix of second central moments written with lattice sums; reason: A⁺ = A⁻¹ for A ≻ 0; the moments are those of the law on p. 9
-- source:
--   Letwin, Reis, Rothvoss, Strongly Log-Concave Measures and Lattices, STOC 2027 submission #401 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/401.pdf, Lemma 3.2, p. 11 (D_{x+Λ,A}: p. 9)

import Mathlib
import Definitions.Def_LogConcaveLattice_Lift_Lattice
import Definitions.Def_LogConcaveLattice_Lift_Gaussian

namespace LogConcaveLattice.Lift

/-- **Lemma 3.2** (p. 11): for a full-rank lattice `Λ ⊆ ℝⁿ`, `x ∈ ℝⁿ` and a symmetric
positive-definite `A`, the covariance of `D_{x+Λ,A}` is minimized at `x = 0`:
`0 ≼ Cov(D_{Λ,A}) ≼ Cov(D_{x+Λ,A})`. -/
theorem lemma_3_2 (n : ℕ) (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (x : V n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    LoewnerLE 0 (mat (dgCov A Λ 0)) ∧ LoewnerLE (mat (dgCov A Λ 0)) (mat (dgCov A Λ x)) := by sorry

end LogConcaveLattice.Lift
