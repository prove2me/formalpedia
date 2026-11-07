-- Prove2me | Theorems.Thm_OnlineShadow_LogRate_lemma_4_5
-- name    : OnlineShadow.LogRate.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:11:26.160443+00:00
-- url     : https://prove2.me/theorems/e49c2540-e5ce-464f-9ff2-a11caa5694a2
-- title:
--   Lemma 4.5 — a bad outcome costs energy
-- statement:
--   Let $\mathcal H=\mathbb C^d$, let $\psi$ be a unit vector on $\mathcal H\otimes\mathcal R$ ($\mathcal R=\mathbb C^r$) purifying the state $\rho=\mathrm{Tr}_{\mathcal R}|\psi\rangle\langle\psi|$, and let $A$ be a single-copy observable with $0\preceq A\preceq1$. On $(\mathcal H\otimes\mathcal R)^{\otimes n}$ let $\overline A$ denote the lift of $A\otimes1_{\mathcal R}$, $\overline X=\overline A-\mathrm{Tr}(A\rho)1$, $\mathsf N$ the number operator and $\mathcal E[\tau]=\frac1n\mathrm{Tr}(\mathsf N\tau)$ the energy relative to $\psi$.
--
--   Let $\varepsilon>0$ with $n\varepsilon^2>4608$, let $\theta,\lambda\in\mathbb R$, and let $F=f_{\theta,\lambda}(\overline A)$ with $f_{\theta,\lambda}(x)=1/(1+e^{\lambda(\theta-\varepsilon/8-x)})$ be the flag operator of the soft binary measurement of $(A,\theta)$. Let $\sigma$ be a positive semidefinite operator (the state before the measurement).
--
--   **Lemma 4.5.** Let $H$ be the operator of a bad outcome: $H=F$ (flag) if $(A,\theta)$ is low, $\mathrm{Tr}(A\rho)\le\theta-\varepsilon/4$; or $H=1-F$ (pass) if $(A,\theta)$ is high, $\mathrm{Tr}(A\rho)>\theta$. Then $\tau=\sqrt H\sigma\sqrt H$ satisfies
--   $$\mathrm{Tr}(\tau)\le2e^{-\lambda\varepsilon/16}\,\mathrm{Tr}(\sigma)+\frac{4608}{\varepsilon^2}\,\mathcal E[\tau].$$
--
--   Reaching a bad leaf of the protocol's tree has either exponentially small probability or forces energy into the post-measurement state.
--
--   Differences from the source:
--   - generalization: τ, σ sub-normalized states of the protocol's tree after/before a bad outcome of ONLINESHADOWTOMOGRAPHY1 → one soft binary measurement of (A, θ) on any positive semidefinite σ, outside the protocol; reason: the proof uses only the measurement, the low/high property and σ ⪰ 0; the tree's states are instances (paper.md R12)
--   - generalization: λ = Θ(εn/√K) > 0 (Algorithm 1) → any real λ; reason: for λ ≤ 0 the bound holds since Tr τ ≤ Tr σ ≤ 2e^{−λε/16} Tr σ; λ > 0 is a special case
--   - encoding: bad outcome with operator H; the high case "follows verbatim" → both cases stated: H = F for a low test, H = 1 − F for a high test; reason: this is Definition 4.3's bad outcome; the conjunction is the lemma for every bad outcome
--   - encoding: ε > 0 (Definition 1.1, standing) → explicit hypothesis 0 < ε; reason: standing assumption of the paper
--   - encoding: $|\psi\rangle$ any purification of $\rho$ on $\mathcal H\otimes\mathcal R$ → ψ : Fin d × Fin r → ℂ with ∑ₓ ‖ψ x‖² = 1 for any r, and ρ := Tr_R |ψ⟩⟨ψ| (marginal ψ); reason: the same objects: every purification is a unit vector on ℂ^d ⊗ ℂ^r and every ρ has one with r = d (paper.md R12)
--   - encoding: Tr(·) of the product → the real part .trace.re; reason: every such trace is of a Hermitian operator or of a product of two Hermitian operators, so it is real and the real part is its value
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Lemma 4.5, p. 12 (proof p. 13)

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_OnlineShadow_LogRate_liftObs
import Definitions.Def_OnlineShadow_LogRate_marginal
import Definitions.Def_OnlineShadow_LogRate_energy
import Definitions.Def_OnlineShadow_LogRate_logistic
import Definitions.Def_OnlineShadow_LogRate_IsLowTest
import Definitions.Def_OnlineShadow_LogRate_IsHighTest

open scoped Kronecker ComplexOrder

namespace OnlineShadow.LogRate

/-- **Lemma 4.5** (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), p.12; proof p.13). Let `ψ` be a unit vector on `H ⊗ R` purifying
`ρ = Tr_R |ψ⟩⟨ψ|`, `A` an effect on `H`, `ε > 0` with `n ε² > 4608`, `θ` and `λ` real, `σ` positive
semidefinite on `(H ⊗ R)^{⊗n}`, and `F = f_{θ,λ}(Ā ⊗ 1_R)` with `f_{θ,λ}(x) = 1/(1 + e^{λ(θ − ε/8 − x)})`.
A bad outcome of the soft binary measurement of `(A, θ)` is the flag `H = F` when `(A, θ)` is low, or
the pass `H = 1 − F` when `(A, θ)` is high; for it, `τ = √H σ √H` satisfies
`Tr(τ) ≤ 2e^{−λε/16} Tr(σ) + (4608/ε²) E[τ]`.

**Formalization Note** Stated for one measurement, outside the protocol: `σ` is the state before it.
Both cases are stated (the paper: "The case of high `(A, θ)` follows verbatim"). `λ` is any real: for
`λ ≤ 0` the bound holds since `Tr τ ≤ Tr σ` (generalization; the protocol has `λ > 0`). `σ` is any
positive semidefinite operator (paper.md R12). Square roots are `cfc Real.sqrt`. -/
theorem lemma_4_5 {d r : ℕ} (ψ : Fin d × Fin r → ℂ) (hψ : ∑ x, ‖ψ x‖ ^ 2 = 1) (n : ℕ)
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : ShadowTomography.UpperBound.IsEffect A)
    (ε θ lam : ℝ) (hε : 0 < ε) (hnε : 4608 < (n : ℝ) * ε ^ 2)
    (σ : Matrix (Fin n → Fin d × Fin r) (Fin n → Fin d × Fin r) ℂ) (hσ : σ.PosSemidef) :
    let F := cfc (logistic (θ - ε / 8) lam) (liftObs n (A ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ)))
    (IsLowTest (marginal ψ) A θ ε →
      (cfc Real.sqrt F * σ * cfc Real.sqrt F).trace.re ≤
        2 * Real.exp (-(lam * ε / 16)) * σ.trace.re +
          4608 / ε ^ 2 * energy ψ n (cfc Real.sqrt F * σ * cfc Real.sqrt F)) ∧
    (IsHighTest (marginal ψ) A θ →
      (cfc Real.sqrt (1 - F) * σ * cfc Real.sqrt (1 - F)).trace.re ≤
        2 * Real.exp (-(lam * ε / 16)) * σ.trace.re +
          4608 / ε ^ 2 * energy ψ n (cfc Real.sqrt (1 - F) * σ * cfc Real.sqrt (1 - F))) := by sorry

end OnlineShadow.LogRate
