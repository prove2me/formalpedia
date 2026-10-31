-- Prove2me | Theorems.Thm_FuchsThesis_Holevo_eq_3_181
-- name    : FuchsThesis.Holevo.eq_3_181
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:58:00.147303+00:00
-- url     : https://prove2.me/theorems/642deea5-1cd4-45a3-b7f1-0cd15023271d
-- title:
--   Eqs. (3.179)–(3.181): $\mathcal L_{\hat\rho}(\hat\Delta)$ is Hermitian and solves the Lyapunov equation
-- statement:
--   Let $\hat\rho_0,\hat\rho_1$ be density operators on a finite-dimensional space and $0<t<1$. Let $\hat\rho=(1-t)\hat\rho_0+t\hat\rho_1$ have eigenvalues $\lambda_j$ and orthonormal eigenbasis $|j\rangle$, and let $\Delta_{jk}=\langle j|\hat\Delta|k\rangle$, $\hat\Delta=\hat\rho_1-\hat\rho_0$. Then:
--
--   1. $\Delta_{jk}=0$ whenever $\lambda_j+\lambda_k=0$;
--   2. the operator
--   $$
--   \mathcal L_{\hat\rho}(\hat\Delta) = \sum_{\{j,k\,|\,\lambda_j+\lambda_k\ne0\}} \frac{2}{\lambda_j+\lambda_k}\,\Delta_{jk}\,|j\rangle\langle k|
--   $$
--   is Hermitian;
--   3. it solves the Lyapunov equation (3.177):
--   $$
--   \tfrac12\big(\hat\rho\,\mathcal L_{\hat\rho}(\hat\Delta)+\mathcal L_{\hat\rho}(\hat\Delta)\,\hat\rho\big)=\hat\Delta .
--   $$
--
--   Although the Lyapunov equation has no solution for a general right-hand side when $\hat\rho$ is singular, it does for $\hat\Delta$, so $\mathcal L_{\hat\rho}(\hat\Delta)$ and $L''(t)$ are defined without any invertibility assumption on $\hat\rho_0,\hat\rho_1$.
--
--   Differences from the source:
--   - encoding: density operators on a D-dimensional Hilbert space → complex matrices over an arbitrary finite index type d with WildeQIT.IsDensityOperator; reason: Lean convention; the same states
--   - encoding: an orthonormal eigenbasis |j⟩ of ρ̂ → the columns of Mathlib's eigenvectorUnitary of ρ̂; reason: the source's argument works for every eigenbasis; Mathlib fixes one
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eqs. (3.177), (3.179)–(3.181), pp.69–70 (PDF pp.78–79)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsThesis_Holevo_mixState
import Definitions.Def_FuchsThesis_Holevo_eigval
import Definitions.Def_FuchsThesis_Holevo_eigCoord
import Definitions.Def_FuchsThesis_Holevo_lyapInv

namespace FuchsThesis.Holevo

/-- Fuchs, arXiv:quant-ph/9601020v1, (3.179)–(3.181), pp.69–70 (PDF pp.78–79): for density
operators `ρ̂0, ρ̂1` and `0 < t < 1`, with `ρ̂ = (1 − t)ρ̂0 + tρ̂1`, eigenvalues `λ_j`, eigenbasis
`|j⟩` and `Δ̂ = ρ̂1 − ρ̂0`:
1. `Δ_jk = ⟨j|Δ̂|k⟩` vanishes whenever `λ_j + λ_k = 0`;
2. the operator `𝓛_ρ̂(Δ̂) = ∑_{λ_j + λ_k ≠ 0} (2/(λ_j + λ_k)) Δ_jk |j⟩⟨k|` of (3.181) is Hermitian;
3. it solves the Lyapunov equation (3.177): `½(ρ̂ 𝓛_ρ̂(Δ̂) + 𝓛_ρ̂(Δ̂) ρ̂) = Δ̂`.

**Formalization Note.** `𝓛_ρ̂` is `lyapInv`, eigenvalues `eigval`, matrix elements `eigCoord`
(Mathlib's eigenbasis of the Hermitian `ρ̂`). The hypothesis `0 < t < 1` is the source's (p.69). -/
theorem eq_3_181 {d : Type} [Fintype d] [DecidableEq d] (ρ0 ρ1 : Matrix d d ℂ)
    (h0 : WildeQIT.IsDensityOperator ρ0) (h1 : WildeQIT.IsDensityOperator ρ1)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (∀ j k, eigval (mixState ρ0 ρ1 t) j + eigval (mixState ρ0 ρ1 t) k = 0 →
        eigCoord (mixState ρ0 ρ1 t) (ρ1 - ρ0) j k = 0) ∧
      (lyapInv (mixState ρ0 ρ1 t) (ρ1 - ρ0)).IsHermitian ∧
      (1 / 2 : ℂ) • (mixState ρ0 ρ1 t * lyapInv (mixState ρ0 ρ1 t) (ρ1 - ρ0) +
          lyapInv (mixState ρ0 ρ1 t) (ρ1 - ρ0) * mixState ρ0 ρ1 t) = ρ1 - ρ0 := by sorry

end FuchsThesis.Holevo
