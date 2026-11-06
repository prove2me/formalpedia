-- Prove2me | Theorems.Thm_MatrixLewis_theorem_3_9
-- name    : MatrixLewis.theorem_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:12:15.921744+00:00
-- url     : https://prove2.me/theorems/81bc30f3-418d-4112-9422-b0935be74ab5
-- title:
--   Theorem 3.9 — well-posedness and analytic dependence
-- statement:
--   Throughout, $A_1,\dots,A_m, C$ are real symmetric $n\times n$ matrices, the $A_i$ satisfy Assumption 3.1 (linearly independent, with $\bigcap_i \ker A_i=\{0\}$), and $q>2$ is real; $p=q/(q-2)$ and $p'=q/2$.
--
--   For every $S\succ0$:
--
--   1. $F_{\mathrm{du}}=F^S_{\mathrm{du}}$ is strictly convex on $\mathbb S^m_{++}$ and has a unique minimizer $M_*(S)$.
--   2. $Z_S:=H_S^*(M_*(S))^{p'-1}$ is positive definite and is the unique maximizer in the definition of $\varphi_q(S)$.
--   3. $(Z_S,M_*(S))$ satisfies $H_S(Z_S)=M_*(S)^{-1}$ and $Z_S^{p-1}=H_S^*(M_*(S))$; the derivative of $\mathcal J$ in $M$ vanishes at $(S,M_*(S))$, and
--   $$
--   \varphi_q(S)=\min_{M\succ0}\mathcal J(S,M)=\mathcal J\bigl(S,M_*(S)\bigr)=-\tfrac12F^S_{\mathrm{pr}}(Z_S).
--   $$
--   4. $\mathcal J$ is real analytic on $\mathbb S^n_{++}\times\mathbb S^m_{++}$, and $S\mapsto M_*(S)$, $S\mapsto Z_S$, $S\mapsto\varphi_q(S)$ are real analytic on $\mathbb S^n_{++}$.
--
--   Every derivative computation of the paper rests on this theorem.
--
--   Differences from the source:
--   - encoding: real analytic on the open cones of symmetric matrices → analytic at 0 of every composition with an affine chart t ↦ base + Σ_j t_j Y_j (Y_j symmetric), matrix-valued maps entrywise; reason: the cones are open in the symmetric matrices, not in all matrices; with a basis of Sⁿ (resp. Sⁿ×Sᵐ) the charts give the usual notion
--   - encoding: 𝒥_M(S, M*(S)) = 0 → d/du 𝒥(S, M* + uV) = 0 at u = 0 for every symmetric V; reason: the derivative in M on Sᵐ is determined by its directional derivatives
--   - encoding: Z_S is the unique maximizer in (9), with log det of singular H_S(Z) = −∞ → Z_S has H_S(Z_S) ≻ 0, its bracket is the greatest element of the set of brackets over Z ⪰ 0 with H_S(Z) ≻ 0, and any such Z with the same bracket equals Z_S; reason: the singular Z have value −∞ and cannot be maximizers
--   - encoding: M*(S), the unique minimizer → the defined dualMin q A S, with the clauses that it is positive definite and minimizes F_du; reason: M*(S) is defined by choice from the unique minimizer; the clauses tie the definition to (i)
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Theorem 3.9, pp.20–21, eq. (18)

import Mathlib
import Definitions.Def_MatrixLewis_Assumption31
import Definitions.Def_MatrixLewis_potential
import Definitions.Def_MatrixLewis_Fpr
import Definitions.Def_MatrixLewis_maximizer

namespace MatrixLewis

/-- **Theorem 3.9** (Well-posedness and analytic dependence; Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), pp.20–21, eq. (18)).
For every `S ≻ 0`:
(i) `F_du = F^S_du` is strictly convex on `Sᵐ₊₊` and has a unique minimizer `M*(S)`;
(ii) `Z_S := H*_S(M*(S))^{p′−1}` is positive definite and is the unique maximizer in eq. (9);
(iii) `(Z_S, M*(S))` satisfies eq. (16), so `H_S(Z_S) = M*(S)⁻¹` and
`Z_S^{p−1} = H*_S(M*(S))`; moreover `𝒥_M(S, M*(S)) = 0` and
`φ_q(S) = min_{M≻0} 𝒥(S, M) = 𝒥(S, M*(S)) = −½F^S_pr(Z_S)`;
(iv) `𝒥` is real analytic on `Sⁿ₊₊ × Sᵐ₊₊`, and `S ↦ M*(S)`, `S ↦ Z_S`, `S ↦ φ_q(S)` are real
analytic on `Sⁿ₊₊`.

**Formalization Note** Standing assumptions of §3 (p.14) are hypotheses. `Sᵐ₊₊` is the set of
positive definite matrices (`Matrix.PosDef` includes symmetry). "Unique maximizer in eq. (9)":
`Z_S ⪰ 0` has `H_S(Z_S) ≻ 0`, its bracket is the greatest element of the bracket set, and any
`Z ⪰ 0` with `H_S(Z) ≻ 0` and the same bracket is `Z_S` (the `Z` with `H_S(Z)` singular have
bracket `−∞` in the paper and are never maximizers). `𝒥_M(S, M*) = 0` is read as vanishing of
every directional derivative `d/du 𝒥(S, M* + uV)` at `0`, `V ∈ Sᵐ`. Real analyticity on the open
cones of the symmetric matrices is read through affine charts: for every base point in the cone
and every finite family of symmetric directions, the composition with
`t ↦ base + ∑ⱼ tⱼ Yⱼ` is analytic at `t = 0` (taking a basis of `Sⁿ`, resp. `Sⁿ × Sᵐ`, gives the
usual notion); matrix-valued maps are analytic entrywise. -/
theorem theorem_3_9 {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (h31 : Assumption31 A) (hq : 2 < q) :
    (∀ S : Matrix (Fin n) (Fin n) ℝ, S.PosDef →
      -- (i)
      (StrictConvexOn ℝ {M : Matrix (Fin m) (Fin m) ℝ | M.PosDef} (Fdu q A S) ∧
        (∃! M : Matrix (Fin m) (Fin m) ℝ,
          M.PosDef ∧ ∀ M' : Matrix (Fin m) (Fin m) ℝ, M'.PosDef → Fdu q A S M ≤ Fdu q A S M') ∧
        (dualMin q A S).PosDef ∧
        ∀ M' : Matrix (Fin m) (Fin m) ℝ, M'.PosDef → Fdu q A S (dualMin q A S) ≤ Fdu q A S M') ∧
      -- (ii)
      ((maximizer q A S).PosDef ∧ (gram A S (maximizer q A S)).PosDef ∧
        IsGreatest (bracketSet q A S) (bracket q A S (maximizer q A S)) ∧
        ∀ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosSemidef → (gram A S Z).PosDef →
          bracket q A S Z = bracket q A S (maximizer q A S) → Z = maximizer q A S) ∧
      -- (iii)
      (gram A S (maximizer q A S) = (dualMin q A S)⁻¹ ∧
        mpow (pExp q - 1) (maximizer q A S) = gramAdj A S (dualMin q A S) ∧
        (∀ V : Matrix (Fin m) (Fin m) ℝ, V.IsHermitian →
          deriv (fun u : ℝ => Jdual q A S (dualMin q A S + u • V)) 0 = 0) ∧
        IsLeast {v | ∃ M : Matrix (Fin m) (Fin m) ℝ, M.PosDef ∧ v = Jdual q A S M}
          (potential q A S) ∧
        potential q A S = Jdual q A S (dualMin q A S) ∧
        potential q A S = -(1 / 2 : ℝ) * Fpr q A S (maximizer q A S))) ∧
    -- (iv)
    (∀ (S : Matrix (Fin n) (Fin n) ℝ) (M : Matrix (Fin m) (Fin m) ℝ), S.PosDef → M.PosDef →
      ∀ (k l : ℕ) (Y : Fin k → Matrix (Fin n) (Fin n) ℝ) (V : Fin l → Matrix (Fin m) (Fin m) ℝ),
        (∀ j, (Y j).IsHermitian) → (∀ j, (V j).IsHermitian) →
        AnalyticAt ℝ (fun tu : (Fin k → ℝ) × (Fin l → ℝ) =>
          Jdual q A (S + ∑ j, tu.1 j • Y j) (M + ∑ j, tu.2 j • V j)) 0) ∧
    (∀ S : Matrix (Fin n) (Fin n) ℝ, S.PosDef →
      ∀ (k : ℕ) (Y : Fin k → Matrix (Fin n) (Fin n) ℝ), (∀ j, (Y j).IsHermitian) →
        (∀ a b : Fin m, AnalyticAt ℝ (fun t : Fin k → ℝ =>
          dualMin q A (S + ∑ j, t j • Y j) a b) 0) ∧
        (∀ a b : Fin n, AnalyticAt ℝ (fun t : Fin k → ℝ =>
          maximizer q A (S + ∑ j, t j • Y j) a b) 0) ∧
        AnalyticAt ℝ (fun t : Fin k → ℝ => potential q A (S + ∑ j, t j • Y j)) 0) := by sorry

end MatrixLewis
