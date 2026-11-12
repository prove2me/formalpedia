-- Prove2me | Theorems.Thm_IsingVectorBalancing_Subgaussian_selectionMatrix_isLorentzian
-- name    : IsingVectorBalancing.Subgaussian.selectionMatrix_isLorentzian
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T17:39:35.780298+00:00
-- url     : https://prove2.me/theorems/f0b67ec4-e9f9-49f6-8a8b-ec0b15c01801
-- title:
--   Contracting a Lorentzian matrix against nonnegative selections gives a Lorentzian matrix
-- statement:
--   Let $C$ be a finite set, $A \in \mathbb{R}^{C \times C}$ a Lorentzian matrix (symmetric, all entries nonnegative, at most one positive eigenvalue, eigenvalues counted with multiplicity), $m \in \mathbb{N}$, and $t_0, \dots, t_{m-1} \in \mathbb{R}_{\ge 0}^{C}$ nonnegative selection vectors. For $c, c' \in C$ let $M_{cc'} = V_A(\mathbf{1}_c, \mathbf{1}_{c'}, t_0, \dots, t_{m-1})$, where $V_A(x_1, \dots, x_k) = \sum_{c : [k] \to C} \prod_i x_i(c(i)) \prod_{i<j} A(c(i), c(j))$ is the selection polynomial of the paper's equation (3) with $k = m+2$, and $\mathbf{1}_c$ is the indicator vector of $c$. Then $M$ is a Lorentzian matrix.
--
--   This is the Hessian form of the discrete Alexandrov–Fenchel inequality (Theorem 5 of the paper): $M$ is the matrix of the symmetric bilinear form $(x, y) \mapsto V_A(x, y, t_0, \dots, t_{m-1})$, and the inequality $V_A(x_1, x_2, \dots)^2 \ge V_A(x_1, x_1, \dots) V_A(x_2, x_2, \dots)$ for $x_2 \ge 0$ is the reverse Cauchy–Schwarz inequality of a form with at most one positive eigenvalue. Here "Lorentzian" is the definition `IsLorentzian` of the definitions bundle `Definitions.Def_IsingVectorBalancing_Subgaussian_Lorentz` (the Hermitian symmetry is asserted there as an existence claim, together with the eigenvalue count); the selection vectors are placed in the third and later slots by `selections`.
-- source:
--   Guo, H., Spielman, D. A., Zhang, X., Subgaussian Vector Balancing by an Ising Model, STOC 2027 submission 1240, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1240.pdf (no DOI), Section 5, Theorem 5 and the sentences before it; the paper derives Theorem 5 from Lee, Oh, Seo, discrete Alexandrov-Fenchel inequality via Lorentzian polynomials, 2025 (cited as [LOS25] in the paper), Theorem 3.1 and Proposition 4.1 (which, as the paper notes, is Branden, P., Huh, J., Lorentzian polynomials, Ann. of Math. 192 (2020), https://doi.org/10.4007/annals.2020.192.3.4, Proposition 4.5); the statement here is the matrix (signature) content of that derivation, not a sentence of those sources

import Definitions.Def_IsingVectorBalancing_Subgaussian_Lorentz

set_option autoImplicit false
namespace IsingVectorBalancing.Subgaussian

theorem selectionMatrix_isLorentzian {C : Type*} [Fintype C] [DecidableEq C] (m : ℕ)
    (A : Matrix C C ℝ) (hA : IsLorentzian A)
    (tail : Fin m → C → ℝ) (htail : ∀ i c, 0 ≤ tail i c) :
    IsLorentzian (Matrix.of fun c c' =>
      selectionPolynomial A (selections (Pi.single c 1) (Pi.single c' 1) tail)) := by
  sorry

end IsingVectorBalancing.Subgaussian
