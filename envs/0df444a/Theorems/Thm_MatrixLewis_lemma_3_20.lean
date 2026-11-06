-- Prove2me | Theorems.Thm_MatrixLewis_lemma_3_20
-- name    : MatrixLewis.lemma_3_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:14:06.569557+00:00
-- url     : https://prove2.me/theorems/b038ae75-aadd-4945-b7b0-dadbadd9f592
-- title:
--   Lemma 3.20 — reduction to one power trace
-- statement:
--   Throughout, $A_1,\dots,A_m, C$ are real symmetric $n\times n$ matrices, the $A_i$ satisfy Assumption 3.1 (linearly independent, with $\bigcap_i \ker A_i=\{0\}$), and $q>2$ is real; $p=q/(q-2)$ and $p'=q/2$.
--
--   Let the data be in normalized position and let $X$, $\eta$, $\dot M$, $\Xi$, $T$, $\psi$ be as in Lemma 3.16, with $Q_I(X)=\operatorname{tr}(\Lambda X^2)$. On $\mathbb R^n\oplus(\mathbb R^m\otimes\mathbb R^n)$ let
--   $$
--   \hat T=\begin{pmatrix}0&T^\top\\T&0\end{pmatrix},\quad \hat X=\begin{pmatrix}-X&0\\0&2\Xi\end{pmatrix},\quad \chi(t)=\operatorname{tr}\bigl|e^{t\hat X/2}\hat Te^{t\hat X/2}\bigr|^q .
--   $$
--   There are absolute constants $C_1,C_2,C_3$ such that:
--
--   1. $\chi=2\psi$, and $D^3\varphi_q(I)[X,X,X]=\frac1{2q}\chi'''(0)-3D^2\varphi_q(I)[X,X^2]-D\varphi_q(I)[X^3]$;
--   2. $\bigl|3D^2\varphi_q(I)[X,X^2]+D\varphi_q(I)[X^3]\bigr|\le C_1\sqrt q\,\|X\|_{\mathrm{op}}\,\eta$;
--   3. $\chi''(0)\le2q\eta$, $\operatorname{tr}(|\hat T|^q\hat X^2)\le C_2\eta$ and $\|\hat X\|_{\mathrm{op}}\le\|X\|_{\mathrm{op}}+C_3\sqrt\eta$.
--
--   These are the inputs for Lemma 3.19 in the proof of self-concordance.
--
--   Differences from the source:
--   - encoding: O(√q), O(η), O(√η) → absolute constants C₁, C₂, C₃ quantified before all data; reason: O(·) hides an absolute constant (p.17)
--   - encoding: D³φ_q(I)[X,X,X], D²φ_q(I)[X,X²], Dφ_q(I)[X³] → derivatives along I + tX, the mixed partial ∂_s∂_t φ_q(I + sX + tX²) at 0, and the derivative along I + tX³; reason: φ_q is real analytic (Theorem 3.9(iv))
--   - encoding: ℝⁿ ⊕ (ℝᵐ ⊗ ℝⁿ), block matrices, e^{tX̂/2} and |Y|^q → index type Fin n ⊕ (Fin m × Fin n), Matrix.fromBlocks and the functional calculus; reason: the same space and block structure; for symmetric matrices these agree with the paper's matrix functions
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Lemma 3.20, pp.33–34

import Mathlib
import Definitions.Def_MatrixLewis_Assumption31
import Definitions.Def_MatrixLewis_potential
import Definitions.Def_MatrixLewis_NormalizedPosition
import Definitions.Def_MatrixLewis_lineDeriv
import Definitions.Def_MatrixLewis_dilation
import Definitions.Def_LiqPremiaEq_opNorm

namespace MatrixLewis

/-- **Lemma 3.20** (Reduction to one power trace; Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), pp.33–34). Let the data, `Λ`, `X`, `η`,
`Ṁ`, `Ξ`, `T` and `ψ` be as in Lemma 3.16, and let `Q_I(X) = tr(ΛX²)`. On `ℝⁿ ⊕ (ℝᵐ ⊗ ℝⁿ)`,
define `T̂ = [[0, Tᵀ], [T, 0]]`, `X̂ = [[−X, 0], [0, 2Ξ]]` and `χ(t) = tr|e^{tX̂/2}T̂e^{tX̂/2}|^q`.
(a) `χ = 2ψ`, and `D³φ_q(I)[X, X, X] = (1/2q)χ‴(0) − 3D²φ_q(I)[X, X²] − Dφ_q(I)[X³]`.
(b) `|3D²φ_q(I)[X, X²] + Dφ_q(I)[X³]| = O(√q)‖X‖_op η`.
(c) `χ″(0) ≤ 2qη`, `tr(|T̂|^q X̂²) = O(η)` and `‖X̂‖_op ≤ ‖X‖_op + O(√η)`.

**Formalization Note** `‖·‖_op` is the published `LiqPremiaEq.opNorm` (the ℓ² operator norm of a real matrix). The three `O`-constants are absolute and quantified before all data.
`DᵏΦ(I)[X, …, X]` are derivatives along `I + tX`; `D²φ_q(I)[X, X²]` is the mixed derivative
`∂_s∂_t φ_q(I + sX + tX²)` at `0` (equal to the bilinear second derivative as `φ_q` is real
analytic, Theorem 3.9(iv)). `ℝⁿ ⊕ (ℝᵐ ⊗ ℝⁿ)` is indexed by `Fin n ⊕ (Fin m × Fin n)`.
Standing assumptions of §3 and normalized position are hypotheses. -/
theorem lemma_3_20 :
    ∃ C₁ C₂ C₃ : ℝ, ∀ {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ),
      (∀ i, (A i).IsHermitian) → Assumption31 A → 2 < q → NormalizedPosition q A →
      ∀ X : Matrix (Fin n) (Fin n) ℝ, X.IsHermitian →
        let φ := potential q A
        let η := lineDeriv 2 φ 1 X
        let χ := chiDil q A X
        -- (a)
        ((χ = fun t => 2 * psiTrace q A X t) ∧
          lineDeriv 3 φ 1 X =
            (1 / (2 * q)) * iteratedDeriv 3 χ 0 - 3 * mixedDeriv2 φ 1 X (X ^ 2)
              - lineDeriv 1 φ 1 (X ^ 3)) ∧
        -- (b)
        |3 * mixedDeriv2 φ 1 X (X ^ 2) + lineDeriv 1 φ 1 (X ^ 3)| ≤
          C₁ * Real.sqrt q * LiqPremiaEq.opNorm X * η ∧
        -- (c)
        (iteratedDeriv 2 χ 0 ≤ 2 * q * η ∧
          (mabsPow q (dilT (scaled A 1)) * dilX q A X ^ 2).trace ≤ C₂ * η ∧
          LiqPremiaEq.opNorm (dilX q A X) ≤ LiqPremiaEq.opNorm X + C₃ * Real.sqrt η) := by sorry

end MatrixLewis
