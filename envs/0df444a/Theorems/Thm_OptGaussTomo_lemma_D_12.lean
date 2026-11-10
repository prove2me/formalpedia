-- Prove2me | Theorems.Thm_OptGaussTomo_lemma_D_12
-- name    : OptGaussTomo.lemma_D_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:07:23.31022+00:00
-- url     : https://prove2.me/theorems/e7035d4f-e183-4a82-8c5c-a90254259db9
-- title:
--   Lemma D.12 — balanced beam splitter: $B(\rho_{\mu,V}\otimes\rho_{\mu,V})B^\dagger=\rho_{0,V}\otimes\rho_{\sqrt2\mu,V}$
-- statement:
--   Let $\rho_{\mu,V}$ be an $m$-mode bosonic Gaussian state with mean $\mu$ and covariance matrix $V$, and let $B$ be a Gaussian unitary on two $m$-mode systems implementing the balanced beam splitter $S_{\mathrm{bs}}=\frac1{\sqrt2}\begin{pmatrix}I&-I\\I&I\end{pmatrix}$. Then
--
--   $$
--   B\big(\rho_{\mu,V}\otimes\rho_{\mu,V}\big)B^\dagger=\rho_{0,V}\otimes\rho_{\sqrt2\mu,V}.
--   $$
--
--   This separates the first moment from the covariance matrix in the protocol of Theorem D.15.
--
--   Differences from the source:
--   - encoding: the Gaussian unitary B corresponding to S_bs → any unitary implementing S_bs in the sense of (D.1) (IsSymplecticUnitary); reason: B is unique up to a phase, which does not affect B X B†
--   - encoding: ρ_{0,V}, ρ_{√2μ,V} → any states σ, τ with GaussianAt σ 0 V and GaussianAt τ (√2μ) V; reason: a Gaussian state is determined by its mean and covariance
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), Lemma D.12 p.55 (pdf p.55)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14
import Definitions.Def_OptGaussTomo_IsSymplecticUnitary
import Definitions.Def_OptGaussTomo_beamSplitter

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14 (InterleavedQuadrature OscillatorCovariance GaussianAt oscillatorTensor)
open QAlgorithms.Papers.Independent.Frontier30.P14 (unitaryCoeff conjugateKernel)

namespace OptGaussTomo

/-- **Lemma D.12** (Balanced beam splitter reduction; Chen, Fanizza, Girardi, Lami, Mele, Walter,
Witteveen, *Optimal tomography of bosonic and fermionic Gaussian states*, arXiv:2607.11847, held
version, sha256 0f7548a2…, Lemma D.12, p.55). Let `ρ_{μ,V}` be an `m`-mode bosonic Gaussian state.
Let `B` be the Gaussian unitary corresponding to the balanced beam splitter acting on two `m`-mode
systems, i.e. to the symplectic matrix `S_bs = (1/√2)[I −I; I I]`. Then
`B(ρ_{μ,V} ⊗ ρ_{μ,V})B† = ρ_{0,V} ⊗ ρ_{√2μ,V}`.

**Formalization Note.** `ρ_{μ,V}` is any state with `GaussianAt ρ μ V` (published `Support50.P14`;
interleaved quadratures, vacuum covariance `I`); it is unique, so `ρ_{0,V}` and `ρ_{√2μ,V}` are
any states `σ`, `τ` with `GaussianAt σ 0 V`, `GaussianAt τ (√2 μ) V`. `B` is any unitary on the
two systems (modes `Fin m ⊕ Fin m`) implementing `S_bs` in the sense of (D.1)
(`IsSymplecticUnitary`); it is unique up to a phase, which does not affect the conclusion. `⊗` is
the published `oscillatorTensor` (system 1 = `Sum.inl`, system 2 = `Sum.inr`), and
`B X B†` is the published kernel conjugation `conjugateKernel`. -/
theorem lemma_D_12 (m : ℕ) (μ : InterleavedQuadrature (Fin m) → ℝ)
    (V : OscillatorCovariance (Fin m)) (ρ σ τ : State (Occupation (Fin m)))
    (hρ : GaussianAt ρ.coefficients μ V) (hσ : GaussianAt σ.coefficients 0 V)
    (hτ : GaussianAt τ.coefficients (Real.sqrt 2 • μ) V)
    (B : Hilbert (Occupation (Fin m ⊕ Fin m)) ≃ₗᵢ[ℂ] Hilbert (Occupation (Fin m ⊕ Fin m)))
    (hB : IsSymplecticUnitary B (beamSplitter m)) :
    conjugateKernel (unitaryCoeff B) (oscillatorTensor ρ.coefficients ρ.coefficients) =
      oscillatorTensor σ.coefficients τ.coefficients := by sorry

end OptGaussTomo
