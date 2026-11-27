-- Prove2me | Theorems.Thm_IncentiveFinNet_Supplement_corollary_2
-- name    : IncentiveFinNet.Supplement.corollary_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:34:06.04033+00:00
-- url     : https://prove2.me/theorems/4e3c3e86-e142-4946-a942-779250f790f9
-- title:
--   Corollary 2 — closed forms of the stable network and prices for a shared $\Sigma$ with all edges allowed
-- statement:
--   Suppose all agents share the covariance $\Sigma_i=\Sigma\succ0$ and all edges are allowed ($\Psi_i = I_n$). Let $\Gamma=\mathrm{diag}(\gamma_1,\dots,\gamma_n)$, and let $(\lambda_i,v_i)_{i\in[n]}$ be an orthonormal eigenbasis of $\Gamma^{-1/2}\Sigma\Gamma^{-1/2}$. Then a stable point exists, and every stable point $(W,P)$ satisfies
--
--   $$
--   \mathrm{vec}(W) = \tfrac12(\Gamma\otimes\Sigma+\Sigma\otimes\Gamma)^{-1}\mathrm{vec}(M+M^{\top}),
--   $$
--   $$
--   W = \Gamma^{-1/2}\Bigl(\sum_{i=1}^n\sum_{j=1}^n \frac{v_i^{\top}\Gamma^{-1/2}(M+M^{\top})\Gamma^{-1/2}v_j}{2(\lambda_i+\lambda_j)}\,v_iv_j^{\top}\Bigr)\Gamma^{-1/2},
--   $$
--   $$
--   \mathrm{vec}(P) = (\Gamma^{-1}\otimes\Sigma^{-1}+\Sigma^{-1}\otimes\Gamma^{-1})^{-1}\mathrm{vec}(\Sigma^{-1}M\Gamma^{-1}-\Gamma^{-1}M^{\top}\Sigma^{-1}),
--   $$
--   $$
--   P = \Gamma^{1/2}\Bigl(\sum_{i=1}^n\sum_{j=1}^n \frac{v_i^{\top}\Gamma^{1/2}(\Sigma^{-1}M\Gamma^{-1}-\Gamma^{-1}M^{\top}\Sigma^{-1})\Gamma^{1/2}v_j}{\lambda_i^{-1}+\lambda_j^{-1}}\,v_iv_j^{\top}\Bigr)\Gamma^{1/2}.
--   $$
--
--   Here $\mathrm{vec}$ stacks columns and $(A\otimes B)_{(i,j),(k,\ell)} = A_{ik}B_{j\ell}$. The stable network thus depends on the beliefs only through the symmetric part $M+M^{\top}$, and it is linear in it. Theorems 7 and 8 rest on these formulas.
--
--   Differences from the source:
--
--   - reading: "(λ_i, v_i) the ith eigenvalue and eigenvector of Γ^{−1/2}ΣΓ^{−1/2}" → every orthonormal eigenbasis: v_i ⬝ v_j = δ_ij and Γ^{−1/2}ΣΓ^{−1/2}v_i = λ_i v_i; reason: the second and fourth formulas hold only for unit eigenvectors; the proof (p.36) writes (K′)⁻¹ = Σ(λ_i + λ_j)⁻¹(v_i ⊗ v_j)(v_i ⊗ v_j)ᵀ, which needs an orthonormal basis
--   - generalization: "the network W can be written …" (existence of the stable point presupposed) → a stable point exists, and every stable point satisfies all four identities; reason: the existence clause is an added conclusion (it follows from Theorem 1 and the proof's invertibility argument); dropping it gives the printed claim
--   - encoding: vec, ⊗, inverses, v_iᵀXv_j and v_iv_jᵀ → vecPair (column stacking over pairs), Matrix.kroneckerMap (· * ·), Matrix.inv, v i ⬝ᵥ (X *ᵥ v j) and vecMulVec (v i) (v j); reason: Lean convention; same quantities (the inverted matrices are invertible)
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, Corollary 2 (Shared Σ, all edges allowed), A.4, pp.35–36 (cited as Corollary A.4 in A.12–A.16)

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting
import Definitions.Def_IncentiveFinNet_Stable
import Definitions.Def_IncentiveFinNet_Supplement_matK
import Definitions.Def_IncentiveFinNet_Supplement_sharedSetting

open Matrix

namespace IncentiveFinNet.Supplement

/-- **Corollary 2 (Shared `Σ`, all edges allowed)**, Jalan, Chakrabarti, Sarkar,
arXiv:2212.06808v3, A.4, pp.35–36 (cited as "Corollary A.4" in A.12–A.16): "Suppose `Σ_i = Σ` and
`Ψ_i = I_n` for all `i ∈ [n]`. Let `(λ_i, v_i)` denote the `i`th eigenvalue and eigenvector of
`Γ^{−1/2}ΣΓ^{−1/2}`. Then, the network `W` can be written in two equivalent ways:
`vec(W) = ½(Γ ⊗ Σ + Σ ⊗ Γ)⁻¹ vec(M + Mᵀ)`,
`W = Γ^{−1/2}(Σ_{i,j} [v_iᵀΓ^{−1/2}(M + Mᵀ)Γ^{−1/2}v_j / (2(λ_i + λ_j))] v_i v_jᵀ)Γ^{−1/2}`.
The prices can be written as:
`vec(P) = (Γ⁻¹ ⊗ Σ⁻¹ + Σ⁻¹ ⊗ Γ⁻¹)⁻¹ vec(Σ⁻¹MΓ⁻¹ − Γ⁻¹MᵀΣ⁻¹)`,
`P = Γ^{1/2}(Σ_{i,j} [v_iᵀΓ^{1/2}(Σ⁻¹MΓ⁻¹ − Γ⁻¹MᵀΣ⁻¹)Γ^{1/2}v_j / (λ_i⁻¹ + λ_j⁻¹)] v_i v_jᵀ)Γ^{1/2}`."

Stated for every `M`, every `Σ ≻ 0`, every `γ > 0` and every orthonormal eigenbasis `(λ_i, v_i)`
of `Γ^{−1/2}ΣΓ^{−1/2}`: a stable point exists, and every stable point `(W, P)` of the setting
`(µ_i, Σ, γ_i)` satisfies all four identities.

**Formalization Note**
* The setting is `sharedSetting M Σ γ` (`Σ_i = Σ`, `J_i = [n]`).
* "The `i`th eigenvalue and eigenvector" is read as an orthonormal eigenbasis
  (`v_i ⬝ v_j = δ_ij`, `Γ^{−1/2}ΣΓ^{−1/2} v_i = λ_i v_i`), as used in the proof (p.36,
  `(K′)⁻¹ = Σ_{i,j} (λ_i + λ_j)⁻¹ (v_i ⊗ v_j)(v_i ⊗ v_j)ᵀ`); for eigenvectors that are not unit
  vectors the second and fourth formulas fail.
* `vec` is `vecPair` (column stacking), `⊗` is `Matrix.kroneckerMap (· * ·)` (p.7), `⁻¹` is
  `Matrix.inv` (the matrices are invertible), `v_iᵀ X v_j` is `v i ⬝ᵥ (X *ᵥ v j)` and `v_i v_jᵀ` is
  `vecMulVec (v i) (v j)`.
* The existence clause is not printed in the corollary; it is what "the network `W`" presupposes
  (Theorem 1 and the proof's invertibility argument). -/
theorem corollary_2 {n : ℕ} (M Sig : Matrix (Fin n) (Fin n) ℝ) (γ : Fin n → ℝ)
    (hγ : ∀ i, 0 < γ i) (hSig : Sig.PosDef) (lam : Fin n → ℝ) (v : Fin n → Fin n → ℝ)
    (hv_orth : ∀ i j, v i ⬝ᵥ v j = if i = j then 1 else 0)
    (hv_eig : ∀ i, (GamInvSqrt γ * Sig * GamInvSqrt γ) *ᵥ v i = lam i • v i) :
    (∃ W P : Matrix (Fin n) (Fin n) ℝ, Stable (sharedSetting M Sig γ hγ hSig) W P) ∧
    ∀ W P : Matrix (Fin n) (Fin n) ℝ, Stable (sharedSetting M Sig γ hγ hSig) W P →
      vecPair W = ((1 / 2 : ℝ) • (Matrix.kroneckerMap (· * ·) (Gam γ) Sig +
          Matrix.kroneckerMap (· * ·) Sig (Gam γ))⁻¹) *ᵥ vecPair (M + Mᵀ) ∧
      W = GamInvSqrt γ * (∑ i, ∑ j,
          ((v i ⬝ᵥ ((GamInvSqrt γ * (M + Mᵀ) * GamInvSqrt γ) *ᵥ v j)) / (2 * (lam i + lam j))) •
            vecMulVec (v i) (v j)) * GamInvSqrt γ ∧
      vecPair P = (Matrix.kroneckerMap (· * ·) (Gam γ)⁻¹ Sig⁻¹ +
          Matrix.kroneckerMap (· * ·) Sig⁻¹ (Gam γ)⁻¹)⁻¹ *ᵥ
            vecPair (Sig⁻¹ * M * (Gam γ)⁻¹ - (Gam γ)⁻¹ * Mᵀ * Sig⁻¹) ∧
      P = GamSqrt γ * (∑ i, ∑ j,
          ((v i ⬝ᵥ ((GamSqrt γ * (Sig⁻¹ * M * (Gam γ)⁻¹ - (Gam γ)⁻¹ * Mᵀ * Sig⁻¹) * GamSqrt γ) *ᵥ
              v j)) / ((lam i)⁻¹ + (lam j)⁻¹)) • vecMulVec (v i) (v j)) * GamSqrt γ := by sorry

end IncentiveFinNet.Supplement
