-- Prove2me | Theorems.Thm_GaussAddit_Noise_eq_22
-- name    : GaussAddit.Noise.eq_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:35.648986+00:00
-- url     : https://prove2.me/theorems/e26a6297-7081-4649-93ec-810db3989286
-- title:
--   Eq. (22) with λ0 of Eq. (34) — every expectation value of the operator Θ of (21) is bounded by λ0 = [(n+1)^k − n^k]^(−m)
-- statement:
--   Throughout, $n\ge 0$ is the noise parameter, $m\ge 0$ the number of channel uses, $\mathcal H^{\otimes m}=\ell^2(\mathbb N^m)$ the Fock space of $m$ bosonic modes with basis $|u\rangle$, $u\in\mathbb N^m$, $D(\vec\mu)=\exp(\vec\mu\cdot\vec a^\dagger-\vec a\cdot\vec\mu^\dagger)$ the multi-mode displacement, and
--   $$\mathcal N_n^{\otimes m}(\rho)=\int d^2\vec\mu\;P_n(\vec\mu)\,D(\vec\mu)\,\rho\,D^\dagger(\vec\mu),\qquad P_n(\vec\mu)=\frac{e^{-|\vec\mu|^2/n}}{(\pi n)^m},$$
--   the $m$-use classical-noise channel ($P_n$ is the point mass at $0$ when $n=0$, so $\mathcal N_0^{\otimes m}$ is the identity). For an operator $A$ and $z\ge1$, $\|A\|_z=(\operatorname{Tr}|A|^z)^{1/z}\in[0,\infty]$.
--
--   Let $k\ge1$ and let $\Theta$ be the operator (21) on the $k$-copy space $(\mathcal H^{\otimes m})^{\otimes k}$. For every vector $\phi$ of that space the integrand defining $\langle\phi|\Theta|\phi\rangle$ is integrable, and
--   $$\big|\langle\phi|\Theta|\phi\rangle\big|\le|\lambda_0|\,\|\phi\|^2,\qquad |\lambda_0|=\left[\frac{1}{(n+1)^k-n^k}\right]^m .$$
--   At $\phi=\psi\otimes\cdots\otimes\psi$ with $\rho=|\psi\rangle\langle\psi|$ the left-hand side is $\operatorname{Tr}\{[\mathcal N_n^{\otimes m}(\rho)]^k\}$ by (20), and the inequality is (22) with the value of $\lambda_0$ from (34).
--
--   This is the spectral step of the proof: $\Theta$ is normal and its eigenvalue of largest modulus is $\lambda_0$.
--
--   Differences from the source:
--   - generalization: Tr{[N(ρ)]^k} = ⟨ψ^{⊗k}|Θ|ψ^{⊗k}⟩ ⩽ |λ0| for the pure input ρ = |ψ⟩⟨ψ| → |⟨φ|Θ|φ⟩| ⩽ |λ0|‖φ‖² for every vector φ of (H^{⊗m})^{⊗k}; reason: specializes to (22) at φ = ψ⊗⋯⊗ψ, by (20)
--   - encoding: |λ0| → its value [(n + 1)^k − n^k]^(−m) from (34); reason: λ0 is defined on p. 3 as an eigenvalue and evaluated on p. 4
--   - encoding: Θ as an operator (21) → its quadratic form, the Gaussian average of Σ_{U,V} φ_U^* ∏_s ⟨U_s|D†(μ⃗_s)D(μ⃗_{s+1})|V_s⟩ φ_V, with explicit integrability; reason: Mathlib has no Hilbert tensor product; a non-integrable integrand would have the junk integral 0
--   - encoding: N_n^{⊗m} as an operator on H^{⊗m} with the integral (14) → the integral (14) on Fock coefficient arrays over ℓ²(ℕ^m), P_n as the law of independent N(0, n/2) real and imaginary parts (Dirac mass at n = 0); reason: Mathlib has no Hilbert tensor product; ℓ²(ℕ)^{⊗m} = ℓ²(ℕ^m) and the same channel on every input
-- source:
--   Giovannetti & Lloyd, Additivity properties of a Gaussian channel, arXiv:quant-ph/0403075v3, p. 3, eq. (22), with λ0 from eq. (34), p. 4

import Mathlib
import Definitions.Def_GaussAddit_Noise_Channel

open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity rankOne)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace GaussAddit.Noise

theorem eq_22 (n : ℝ) (hn : 0 ≤ n) (m k : ℕ) (hk : 1 ≤ k) (φ : Hilbert (Fin k → Occ m)) :
    Integrable (thetaIntegrand φ) (Measure.pi fun _ : Fin k => noiseLaw n m) ∧
      ‖thetaForm n m k φ‖ ≤ ((n + 1) ^ k - n ^ k)⁻¹ ^ m * ‖φ‖ ^ 2 := by sorry

end GaussAddit.Noise
