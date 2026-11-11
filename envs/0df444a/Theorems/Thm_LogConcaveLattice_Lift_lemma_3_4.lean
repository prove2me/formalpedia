-- Prove2me | Theorems.Thm_LogConcaveLattice_Lift_lemma_3_4
-- name    : LogConcaveLattice.Lift.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:01:39.307951+00:00
-- url     : https://prove2.me/theorems/c8325389-1a4e-483b-897f-caf72ada9367
-- title:
--   Lemma 3.4 — an optimal $A\succcurlyeq0$ with lattice subspace $E=\operatorname{im}A$ and $A^+\operatorname{Cov}(D_{\Lambda\cap E,A})A^+\succcurlyeq\frac1{2\pi e}\mathrm{Id}_E$
-- statement:
--   Let $\Lambda\subseteq\mathbb R^n$ be a non-zero lattice (of any rank) with $\det\Lambda\le1$, the determinant computed in the span of $\Lambda$. Then there exists a matrix $A\in\mathbb R^{n\times n}$ with $A\succcurlyeq0$ such that $E=\operatorname{im}(A)$ is a nonzero lattice subspace of $\Lambda$, i.e. $\operatorname{span}_{\mathbb R}(\Lambda\cap E)=E\ne\{0\}$, and
--   $$A^+\operatorname{Cov}(D_{\Lambda\cap E,A})\,A^+\succcurlyeq\frac1{2\pi e}\,\mathrm{Id}_E .\tag{3.6}$$
--   Here $A^+$ is the Moore–Penrose pseudoinverse, $D_{\Lambda\cap E,A}$ is the discrete Gaussian on $\Lambda\cap E$ with $\mathbb P(Y=y)\propto\rho_A(y)=e^{-\pi\langle y,A^+y\rangle}$, and $\mathrm{Id}_E$ acts on $\mathbb R^n$ as the orthogonal projection $\Pi_E$.
--
--   Applied to $\Lambda$ with weakly stable dual (so $\det\Lambda\le1$), this gives the subspace $E$ on which the strongly log-concave density is first constructed in the proof of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: Id_E regarded as an operator on Rⁿ → the orthogonal projection Π_E onto E; reason: the source's convention (p. 6: an operator on E is extended by zero on E⊥); same instances
--   - encoding: det(Λ) for a lattice of any rank → the Gram determinant √det(⟨bᵢ,bⱼ⟩) of a lattice basis; reason: the determinant computed in the span (pp. 1, 7); same instances
-- source:
--   Letwin, Reis, Rothvoss, Strongly Log-Concave Measures and Lattices, STOC 2027 submission #401 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/401.pdf, Lemma 3.4 and (3.6), p. 12 (proof pp. 12–13)

import Mathlib
import Definitions.Def_LogConcaveLattice_Lift_Lattice
import Definitions.Def_LogConcaveLattice_Lift_Gaussian

namespace LogConcaveLattice.Lift

/-- **Lemma 3.4** (p. 12): for every non-zero lattice `Λ ⊆ ℝⁿ` (any rank) with `det Λ ≤ 1`
there is a matrix `A ≽ 0` such that `E = im(A)` is a nonzero lattice subspace of `Λ` and
`A⁺ Cov(D_{Λ∩E,A}) A⁺ ≽ (1/(2πe)) Id_E`, where `Id_E` acts on `ℝⁿ` as `Π_E`. -/
theorem lemma_3_4 (n : ℕ) (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ] (hΛ : Λ ≠ ⊥)
    (hdet : latticeDet Λ ≤ 1) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, A.PosSemidef ∧ matIm A ≠ ⊥ ∧
      IsLatticeSubspace Λ (matIm A) ∧
      LoewnerLE
        ((1 / (2 * Real.pi * Real.exp 1)) •
          ((matIm A).starProjection : V n →L[ℝ] V n).toLinearMap)
        (mat (pinv A * dgCov A (interSubspace Λ (matIm A)) 0 * pinv A)) := by sorry

end LogConcaveLattice.Lift
