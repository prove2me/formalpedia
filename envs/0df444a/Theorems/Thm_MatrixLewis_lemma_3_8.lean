-- Prove2me | Theorems.Thm_MatrixLewis_lemma_3_8
-- name    : MatrixLewis.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:10:09.717558+00:00
-- url     : https://prove2.me/theorems/1609089f-92c6-4959-b542-26935c01dd17
-- title:
--   Lemma 3.8 — weak duality and the gap identity
-- statement:
--   Throughout, $A_1,\dots,A_m, C$ are real symmetric $n\times n$ matrices, the $A_i$ satisfy Assumption 3.1 (linearly independent, with $\bigcap_i \ker A_i=\{0\}$), and $q>2$ is real; $p=q/(q-2)$ and $p'=q/2$.
--
--   Let $S\succ0$, let $Z\succeq0$ with $H_S(Z)\succ0$, and let $M\succ0$. Put $A=H_S^*(M)$ and let $\lambda_1,\dots,\lambda_m$ be the eigenvalues of $M^{1/2}H_S(Z)M^{1/2}$. Then all $\lambda_i>0$,
--   $$
--   F_{\mathrm{pr}}(Z)+F_{\mathrm{du}}(M)=\Bigl(\frac1p\operatorname{tr}Z^p+\frac1{p'}\operatorname{tr}A^{p'}-\operatorname{tr}(AZ)\Bigr)+\sum_{i=1}^m\varrho(\lambda_i)\ \ge\ 0,
--   $$
--   and equality holds if and only if
--   $$
--   H_S^*(M)=Z^{p-1},\qquad M^{-1}=H_S(Z).
--   $$
--   At the primal point $Z=A^{p'-1}$ determined by $M$, the first term vanishes, $\operatorname{tr}A^{p'}=\operatorname{tr}\Psi$, and
--   $$
--   F_{\mathrm{pr}}(A^{p'-1})+F_{\mathrm{du}}(M)=\Delta(M).
--   $$
--
--   The lemma is weak duality between the potential and its dual with an explicit gap.
--
--   **Formalization Note** The paper's matrix $A=H_S^*(M)$ is called `G` (the data are `A`).
--
--   Differences from the source:
--   - encoding: λ₁,…,λ_m > 0 are the eigenvalues of M^{1/2}H_S(Z)M^{1/2} → eigenvalues of that symmetric matrix for any proof of its symmetry, with their positivity among the conclusions; reason: Lean's eigenvalues need a symmetry proof; the positivity the page presupposes is a consequence
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Lemma 3.8, pp.19–20, eqs. (15)–(17)

import Mathlib
import Definitions.Def_MatrixLewis_Assumption31
import Definitions.Def_MatrixLewis_Fpr
import Definitions.Def_MatrixLewis_Fdu
import Definitions.Def_MatrixLewis_gapDelta

namespace MatrixLewis

/-- **Lemma 3.8** (Weak duality and the gap identity; Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), pp.19–20, eqs. (15)–(17)).
Let `S ≻ 0`, let `Z ⪰ 0` with `H_S(Z) ≻ 0`, and let `M ≻ 0`. Put `A = H*_S(M)` (here `G`), and
let `λ₁, …, λ_m > 0` be the eigenvalues of `M^{1/2} H_S(Z) M^{1/2}`. Then
`F_pr(Z) + F_du(M) = ((1/p) tr Z^p + (1/p′) tr A^{p′} − tr(AZ)) + ∑ᵢ ϱ(λᵢ) ≥ 0`, with equality iff
`H*_S(M) = Z^{p−1}` and `M⁻¹ = H_S(Z)`. At the primal point `Z = A^{p′−1}` determined by `M`,
the first term vanishes, `tr A^{p′} = tr Ψ`, and `F_pr(A^{p′−1}) + F_du(M) = Δ(M)`.

**Formalization Note** Standing assumptions of §3 (p.14): symmetric data satisfying
Assumption 3.1 and real `q > 2`. The paper's matrix `A = H*_S(M)` is called `G` here (the data
are `A`). The eigenvalues are those of the symmetric matrix `Ψ_Z = M^{1/2}H_S(Z)M^{1/2}`, for any
proof `hΨ` of its symmetry; their positivity is part of the conclusion. -/
theorem lemma_3_8 {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (h31 : Assumption31 A) (hq : 2 < q)
    (S Z : Matrix (Fin n) (Fin n) ℝ) (M : Matrix (Fin m) (Fin m) ℝ)
    (hS : S.PosDef) (hZ : Z.PosSemidef) (hHZ : (gram A S Z).PosDef) (hM : M.PosDef) :
    let G := gramAdj A S M
    let Ψ := mpow (1 / 2 : ℝ) M * gram A S Z * mpow (1 / 2 : ℝ) M
    let Z₀ := primalOf q A S M
    (∀ hΨ : Ψ.IsHermitian,
      (∀ i, 0 < hΨ.eigenvalues i) ∧
      Fpr q A S Z + Fdu q A S M =
        ((1 / pExp q) * (mpow (pExp q) Z).trace + (1 / pDual q) * (mpow (pDual q) G).trace
          - (G * Z).trace) + ∑ i, rho (hΨ.eigenvalues i)) ∧
    0 ≤ Fpr q A S Z + Fdu q A S M ∧
    (Fpr q A S Z + Fdu q A S M = 0 ↔ (gramAdj A S M = mpow (pExp q - 1) Z ∧ M⁻¹ = gram A S Z)) ∧
    ((1 / pExp q) * (mpow (pExp q) Z₀).trace + (1 / pDual q) * (mpow (pDual q) G).trace
        - (G * Z₀).trace = 0 ∧
      (mpow (pDual q) G).trace = (gapMatrix q A S M).trace ∧
      Fpr q A S Z₀ + Fdu q A S M = gapDelta q A S M) := by sorry

end MatrixLewis
