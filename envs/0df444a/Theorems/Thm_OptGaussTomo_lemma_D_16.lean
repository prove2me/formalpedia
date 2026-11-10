-- Prove2me | Theorems.Thm_OptGaussTomo_lemma_D_16
-- name    : OptGaussTomo.lemma_D_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:07:40.667743+00:00
-- url     : https://prove2.me/theorems/784c2cde-43cd-4f3f-96e3-a8756ed0d4d2
-- title:
--   Lemma D.16 — average fidelity bound under $Q$: $\mathbf E_{\psi\sim Q}\mathbf E_{\hat\psi}|\langle\psi|\hat\psi\rangle|^{2k}\le d_{n+2m+1,m}/d_{n+2m+1+k,m}$
-- statement:
--   Let $m\ge1$ and $n,k\in\mathbb N$. Let $d\psi$ be a symplectically invariant measure on the set $\mathcal G^0_m$ of pure mean-zero $m$-mode bosonic Gaussian states, normalized so that
--
--   $$
--   dQ(\psi)=\frac{|\langle\psi|0\rangle|^{4m+2}\,d\psi}{\int|\langle\psi'|0\rangle|^{4m+2}\,d\psi'}
--   $$
--
--   is a probability measure ($|0\rangle$ the vacuum; this is (D.27)). Let $\mu$ be any measurement on $n$ copies whose estimates $\hat\psi$ are pure states, with outcome law $P_\psi$ on $|\psi\rangle\langle\psi|^{\otimes n}$. Then
--
--   $$
--   \mathbf E_{\psi\sim Q}\,\mathbf E_{\hat\psi\sim P_\psi}\,|\langle\psi|\hat\psi\rangle|^{2k}\ \le\ \frac{d_{n+2m+1,m}}{d_{n+2m+1+k,m}},
--   $$
--
--   with $d_{n,m}$ the formal degrees (D.12). Since no invariant probability measure exists on $\mathcal G^0_m$, the weighting by the vacuum overlap replaces the uniform average of Lemma C.7 in the proof of Theorem 5.2.
--
--   **Formalization Note** $d\psi$ is any measure on states that is concentrated on $\mathcal G^0_m$, invariant under conjugation by every symplectic Gaussian unitary, and has $0<\int|\langle\psi|0\rangle|^{4m+2}d\psi<\infty$; the invariant measure is unique up to scale and $Q$ does not depend on the scale. $|\langle\psi|0\rangle|^2=\langle0|\rho|0\rangle$ for $\rho=|\psi\rangle\langle\psi|$, and $|\langle\psi|\hat\psi\rangle|=F(\psi,\hat\psi)$.
--
--   Differences from the source:
--   - encoding: m modes → m ≥ 1; reason: an m-mode system has at least one mode; the paper writes m ∈ ℕ+ (Lemma D.14)
--   - encoding: dQ(ψ) = d_{2m+1,m}|⟨ψ|0⟩|^{4m+2} dψ with the Haar normalization of Lemma D.5 → Q = Z⁻¹|⟨ψ|0⟩|^{4m+2}ν for every invariant measure ν on states concentrated on G⁰_m with 0 < Z := ∫|⟨ψ|0⟩|^{4m+2}dν < ∞; reason: the invariant measure is unique up to scale and Q is scale free; the guard excludes only measures for which Q is undefined
--   - encoding: the estimate ψ̂ from the measurement μ → any POVM with state outcomes whose outcome law on every density is concentrated on pure states; |⟨ψ|ψ̂⟩| as the root fidelity; reason: the paper's estimates are pure; on pure states F = |⟨ψ|ψ̂⟩|
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), Lemma D.16 p.60 (pdf p.60), eq. (D.27) p.60, eq. (D.12) p.46

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14
import Definitions.Def_WildeQIT_Schumacher_tensorPow
import Definitions.Def_BosonicLearn_FockPOVM
import Definitions.Def_OptGaussTomo_rootFidelity
import Definitions.Def_OptGaussTomo_dBose
import Definitions.Def_OptGaussTomo_IsSymplecticUnitary

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity rankOne)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14 (OscillatorCovariance GaussianAt)
open QAlgorithms.Papers.Independent.Frontier30.P14 (unitaryCoeff conjugateKernel)
open MeasureTheory
open scoped ENNReal

namespace OptGaussTomo

/-- **Lemma D.16** (Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, *Optimal tomography of
bosonic and fermionic Gaussian states*, arXiv:2607.11847, held version, sha256 0f7548a2…,
Lemma D.16, p.60, with (D.27), p.60, and (D.12), p.46). Suppose that `ψ` is distributed according to
`Q` as in (D.27), `dQ(ψ) = d_{2m+1,m} |⟨ψ|0⟩|^{4m+2} dψ`, and `ψ̂` denotes the estimate from the
measurement `µ` on `n` copies of `ψ`. Then
`E_{ψ∼Q} E_{ψ̂∼P_ψ} |⟨ψ|ψ̂⟩|^{2k} ≤ d_{n+2m+1,m}/d_{n+2m+1+k,m}`, with `d_{n,m}` given in Lemma D.5.

**Formalization Note.** `dψ` is the Sp(2m)-invariant measure on the set `G⁰_m` of pure mean-zero
Gaussian states; it is unique up to a positive factor, and the source fixes the factor through a
Haar normalization of Sp(2m) under which `Q` is a probability measure. Here `ν` is **any** measure on
the published `State (Occupation (Fin m))` (trace-norm Borel σ-algebra) that is concentrated on
`G⁰_m`, invariant under conjugation by every symplectic Gaussian unitary (`IsSymplecticUnitary`,
(D.1)), and has `0 < Z := ∫ |⟨ψ|0⟩|^{4m+2} dν < ∞`; then `Q = Z⁻¹ |⟨ψ|0⟩|^{4m+2} ν`, which is
(D.27) for the source's normalization, and the statement does not depend on the scale of `ν`.
`|⟨ψ|0⟩|² = ⟨0|ρ|0⟩` for `ρ = |ψ⟩⟨ψ|` and the vacuum `|0⟩` (Fock label `0`). `µ` is any POVM on `n`
copies whose estimates are pure states (its outcome law on every density is concentrated on rank-one
projectors); `|⟨ψ|ψ̂⟩| = F(ψ, ψ̂)`, the root fidelity, on pure states. `P_ψ` is the outcome law on
`|ψ⟩⟨ψ|^{⊗n}`. The expectations are `ℝ≥0∞`-valued integrals of nonnegative integrands.
`d_{n,m}` is (D.12) (`dBose`); both arguments are `≥ 2m + 1`. `k` is any natural number. -/
theorem lemma_D_16 (m n k : ℕ) (hm : 1 ≤ m) (ν : Measure (State (Occupation (Fin m))))
    (hν_supp : ν {ρ | ¬ ((∃ u : Hilbert (Occupation (Fin m)), ‖u‖ = 1 ∧ ρ.coefficients = rankOne u) ∧
        ∃ V : OscillatorCovariance (Fin m), GaussianAt ρ.coefficients 0 V)} = 0)
    (hν_inv : ∀ (U : Hilbert (Occupation (Fin m)) ≃ₗᵢ[ℂ] Hilbert (Occupation (Fin m)))
        (S : OscillatorCovariance (Fin m)), IsSymplecticUnitary U S →
        ∀ A : Set (State (Occupation (Fin m))), MeasurableSet A →
          ν {ρ | ∃ σ ∈ A, σ.coefficients = conjugateKernel (unitaryCoeff U) ρ.coefficients} = ν A)
    (hZ_pos : 0 < ∫⁻ ρ, ENNReal.ofReal
        ((ρ.coefficients (fun _ => 0) (fun _ => 0)).re ^ (2 * m + 1)) ∂ν)
    (hZ_fin : ∫⁻ ρ, ENNReal.ofReal
        ((ρ.coefficients (fun _ => 0) (fun _ => 0)).re ^ (2 * m + 1)) ∂ν < ⊤)
    (μ : BosonicLearn.FockPOVM (Fin n → Occupation (Fin m)) (State (Occupation (Fin m))))
    (hμ : ∀ ρ, IsDensity ρ → μ.law ρ
        {σ | ¬ ∃ u : Hilbert (Occupation (Fin m)), ‖u‖ = 1 ∧ σ.coefficients = rankOne u} = 0) :
    ∫⁻ ρ, (ENNReal.ofReal ((ρ.coefficients (fun _ => 0) (fun _ => 0)).re ^ (2 * m + 1)) /
          ∫⁻ ρ', ENNReal.ofReal
            ((ρ'.coefficients (fun _ => 0) (fun _ => 0)).re ^ (2 * m + 1)) ∂ν) *
        ∫⁻ σ, ENNReal.ofReal (rootFidelity ρ.coefficients σ.coefficients ^ (2 * k))
          ∂(μ.law (WildeQIT.Schumacher.tensorPow n ρ.coefficients)) ∂ν ≤
      ENNReal.ofReal (dBose (n + 2 * m + 1) m / dBose (n + 2 * m + 1 + k) m) := by sorry

end OptGaussTomo
