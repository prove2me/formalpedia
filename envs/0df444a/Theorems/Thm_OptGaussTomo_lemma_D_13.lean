-- Prove2me | Theorems.Thm_OptGaussTomo_lemma_D_13
-- name    : OptGaussTomo.lemma_D_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:07:51.23432+00:00
-- url     : https://prove2.me/theorems/00ec4722-6afa-4c28-8957-c1b891169659
-- title:
--   Lemma D.13 — generaldyne measurement with seed $W$: $X\sim N(\mu,(V+W)/2)$
-- statement:
--   Let $W$ be a valid $2m\times2m$ bosonic covariance matrix. There is a POVM on $\mathbb R^{2m}$ (the generaldyne measurement with seed $W$) such that, if the input is an $m$-mode Gaussian state $\rho_{\mu,V}$, the outcome $X\in\mathbb R^{2m}$ is a Gaussian random vector with $\mathbf EX=\mu$ and $\mathrm{Cov}(X)=(V+W)/2$, i.e.
--
--   $$
--   X\sim N\Big(\mu,\frac{V+W}2\Big),\qquad \mathbf E\,e^{i\langle t,X\rangle}=\exp\Big(i\langle t,\mu\rangle-\tfrac12\,t^{\mathsf T}\tfrac{V+W}2\,t\Big)\ \ \text{for all }t\in\mathbb R^{2m}.
--   $$
--
--   Heterodyne detection is the case $W=I$.
--
--   Differences from the source:
--   - encoding: X ∼ N(μ, (V + W)/2), with E X = μ and Cov(X) = (V + W)/2 → the characteristic function of the outcome law equals exp(i⟨t, μ⟩ − ½ tᵀ((V + W)/2)t) for every t; reason: the characteristic function determines the law, which determines the mean and covariance
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), Lemma D.13 p.55 (pdf p.55)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Definitions.Def_BosonicLearn_FockPOVM
import Definitions.Def_OptGaussTomo_IsValidCov

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14 (InterleavedQuadrature OscillatorCovariance GaussianAt)
open MeasureTheory

namespace OptGaussTomo

/-- **Lemma D.13** (Generaldyne measurement; Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen,
*Optimal tomography of bosonic and fermionic Gaussian states*, arXiv:2607.11847, held version,
sha256 0f7548a2…, Lemma D.13, p.55). Let `W` be a valid `2m × 2m` bosonic covariance matrix. There
exists a POVM on `ℝ^{2m}`, called the generaldyne measurement with seed `W`, with the following
property. If the input is an `m`-mode Gaussian state `ρ_{μ,V}`, then the measurement outcome
`X ∈ ℝ^{2m}` is a classical Gaussian random variable with `E X = μ`, `Cov(X) = (V + W)/2`.
Equivalently, `X ∼ N(μ, (V + W)/2)`.

**Formalization Note.** `ℝ^{2m}` is the space of functions on the interleaved quadratures
`Fin m × Fin 2` (Borel σ-algebra). The law `N(μ, Σ)` is specified by its characteristic function
`E e^{i⟨t, X⟩} = exp(i⟨t, μ⟩ − ½ tᵀ Σ t)` for every `t`, which determines it (and also covers a
singular `Σ`); the mean and covariance clauses follow from the law. Valid covariance:
`IsValidCov`; Gaussian state: published `GaussianAt` (vacuum covariance `I`). -/
theorem lemma_D_13 (m : ℕ) (W : OscillatorCovariance (Fin m)) (hW : IsValidCov W) :
    ∃ E : BosonicLearn.FockPOVM (Occupation (Fin m)) (InterleavedQuadrature (Fin m) → ℝ),
      ∀ (ρ : State (Occupation (Fin m))) (μ : InterleavedQuadrature (Fin m) → ℝ)
        (V : OscillatorCovariance (Fin m)), GaussianAt ρ.coefficients μ V →
        ∀ t : InterleavedQuadrature (Fin m) → ℝ,
          ∫ x, Complex.exp (Complex.I * ((∑ a, t a * x a : ℝ) : ℂ)) ∂(E.law ρ.coefficients) =
            Complex.exp (Complex.I * ((∑ a, t a * μ a : ℝ) : ℂ) -
              (((1 / 2 : ℝ) * ∑ a, ∑ b, t a * ((1 / 2 : ℝ) • (V + W)) a b * t b : ℝ) : ℂ)) := by sorry

end OptGaussTomo
