-- Prove2me | Theorems.Thm_MatrixLewis_lemma_3_16
-- name    : MatrixLewis.lemma_3_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:15:22.813204+00:00
-- url     : https://prove2.me/theorems/52a18287-14c9-4439-beb9-725f956ecddc
-- title:
--   Lemma 3.16 — second derivative along exponential curves
-- statement:
--   Throughout, $A_1,\dots,A_m, C$ are real symmetric $n\times n$ matrices, the $A_i$ satisfy Assumption 3.1 (linearly independent, with $\bigcap_i \ker A_i=\{0\}$), and $q>2$ is real; $p=q/(q-2)$ and $p'=q/2$.
--
--   Let the data be in normalized position, with $Z=Z_I$, $W=W_I$, $\Gamma=\Gamma_I$, $\Lambda=\Lambda_I$, and let $T$ be the row operator of $B_i=B_i(I)$. Let $X\in\mathbb S^n$ with squared local norm $Q_I(X)=\operatorname{tr}(X\Lambda X)$, and put
--   $$
--   \eta:=D^2\varphi_q(I)[X,X],\quad \dot M:=\tfrac{d}{dt}M_*(I+tX)\big|_{t=0},\quad \Xi:=\tfrac12(\dot M\otimes I_n-I_m\otimes X),
--   $$
--   $$
--   \tilde T_t:=e^{t\Xi}Te^{-tX/2},\qquad \psi(t):=\operatorname{tr}\bigl((\tilde T_t^\top\tilde T_t)^{p'}\bigr).
--   $$
--   Then $\mathcal J_M(I,I_m)=0$ and $D^2\mathcal J(I,I_m)[(X,\dot M),(0,\mathcal V)]=0$ for every $\mathcal V\in\mathbb S^m$. For every $t\in\mathbb R$,
--   $$
--   \mathcal J\bigl(e^{tX},e^{t\dot M}\bigr)=-\frac t2\operatorname{tr}\dot M+\frac1q\psi(t)-\frac m2 .
--   $$
--   Moreover $\psi''(0)=q(\eta-Q_I(X))$, $Q_I(X)\le\eta$, and $\|\dot M\|_F^2=O(\eta)$: there is an absolute constant $C$ with $\|\dot M\|_F^2\le C\eta$.
--
--   Differences from the source:
--   - encoding: ‖Ṁ‖²_F = O(η) → ∃ C, quantified before all data, with Σ_{ab} Ṁ_{ab}² ≤ Cη; reason: O(·) hides an absolute constant (p.17)
--   - encoding: 𝒥_M(I, I_m) = 0 and D²𝒥(I, I_m)[(X, Ṁ), (0, 𝒱)] = 0 → d/du 𝒥(I, I_m + u𝒱) = 0 and ∂_s∂_u 𝒥(I + sX, I_m + sṀ + u𝒱) = 0 at 0, for symmetric 𝒱; reason: 𝒥 is real analytic (Theorem 3.9(iv)), so these partials are the Fréchet derivatives
--   - encoding: Ṁ = d/dt M*(I + tX)|₀; η = D²φ_q(I)[X, X] → entrywise derivative; second derivative of t ↦ φ_q(I + tX) at 0; reason: analyticity of M* and φ_q
--   - encoding: e^{tX}, e^{tΞ}, matrix powers, ℝᵐ ⊗ ℝⁿ and M ⊗ Y → functional calculus (mexp, mpow), index type Fin m × Fin n and Matrix.kroneckerMap; reason: for symmetric matrices these agree with the paper's matrix functions; same index order as the row operator
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Lemma 3.16, pp.25–27, eqs. (33)–(36)

import Mathlib
import Definitions.Def_MatrixLewis_Assumption31
import Definitions.Def_MatrixLewis_potential
import Definitions.Def_MatrixLewis_Fdu
import Definitions.Def_MatrixLewis_localNormSq
import Definitions.Def_MatrixLewis_NormalizedPosition
import Definitions.Def_MatrixLewis_lineDeriv
import Definitions.Def_MatrixLewis_expCurve

namespace MatrixLewis

/-- **Lemma 3.16** (The second derivative along exponential curves; Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), pp.25–27,
eqs. (33)–(36)). Let the data be in normalized position, with `Z = Z_I`, `W = W_I`, `Γ = Γ_I`,
`Λ = Λ_I`, and let `T` be the row operator of the `Bᵢ = Bᵢ(I)`. Let `X ∈ Sⁿ` with squared local
norm `Q_I(X) = tr(XΛX)`, and put `η := D²φ_q(I)[X, X]`, `Ṁ := d/dt M*(I + tX)|_{t=0}`,
`Ξ := ½(Ṁ ⊗ Iₙ − I_m ⊗ X)`, `T̃_t := e^{tΞ}Te^{−tX/2}`, `ψ(t) := tr((T̃_tᵀT̃_t)^{p′})`. Then
`𝒥_M(I, I_m) = 0`, and `D²𝒥(I, I_m)[(X, Ṁ), (0, 𝒱)] = 0` for every `𝒱 ∈ Sᵐ`. For every `t ∈ ℝ`,
`𝒥(e^{tX}, e^{tṀ}) = −(t/2) tr Ṁ + (1/q)ψ(t) − m/2`. Moreover `ψ″(0) = q(η − Q_I(X))`,
`Q_I(X) ≤ η`, and `‖Ṁ‖²_F = O(η)`.

**Formalization Note** `O(η)` is an absolute constant `C`, quantified before all data
(`‖Ṁ‖²_F ≤ Cη`). `D²φ_q(I)[X, X]` is the second derivative along `I + tX`; `𝒥_M(I, I_m) = 0` is
vanishing of `d/du 𝒥(I, I_m + u𝒱)` at `0` for every `𝒱 ∈ Sᵐ`; the mixed derivative
`D²𝒥(I, I_m)[(X, Ṁ), (0, 𝒱)]` is `∂_s ∂_u 𝒥(I + sX, I_m + sṀ + u𝒱)` at `0` (both read through
the real analyticity of `𝒥`, Theorem 3.9(iv)). `Ṁ` is the entrywise derivative; exponentials are
the functional calculus `mexp`. Standing assumptions of §3 are hypotheses. -/
theorem lemma_3_16 :
    ∃ C₁₆ : ℝ, ∀ {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ),
      (∀ i, (A i).IsHermitian) → Assumption31 A → 2 < q → NormalizedPosition q A →
      ∀ X : Matrix (Fin n) (Fin n) ℝ, X.IsHermitian →
        let η := lineDeriv 2 (potential q A) 1 X
        let Md := dualVelocity q A X
        let ψ := psiTrace q A X
        (∀ V : Matrix (Fin m) (Fin m) ℝ, V.IsHermitian →
          deriv (fun u : ℝ => Jdual q A 1 (1 + u • V)) 0 = 0) ∧
        (∀ V : Matrix (Fin m) (Fin m) ℝ, V.IsHermitian →
          deriv (fun s : ℝ => deriv (fun u : ℝ =>
            Jdual q A (1 + s • X) (1 + s • Md + u • V)) 0) 0 = 0) ∧
        (∀ t : ℝ, Jdual q A (mexp (t • X)) (mexp (t • Md)) =
          -(t / 2) * Md.trace + (1 / q) * ψ t - (m : ℝ) / 2) ∧
        iteratedDeriv 2 ψ 0 = q * (η - localNormSq q A 1 X) ∧
        localNormSq q A 1 X ≤ η ∧
        ∑ a, ∑ b, Md a b ^ 2 ≤ C₁₆ * η := by sorry

end MatrixLewis
