-- Prove2me | Theorems.Thm_GaussAddit_Noise_eq_16_17
-- name    : GaussAddit.Noise.eq_16_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:43.653405+00:00
-- url     : https://prove2.me/theorems/6892cd5a-0267-4272-b351-dbe1ae8cfe77
-- title:
--   Eqs. (16)–(17) — for a pure input, Tr{[N_n^{⊗m}(ρ)]^k} is the Gaussian average of the cyclic product of the overlaps ⟨ψ|D†(μ⃗_s)D(μ⃗_{s+1})|ψ⟩
-- statement:
--   Throughout, $n\ge 0$ is the noise parameter, $m\ge 0$ the number of channel uses, $\mathcal H^{\otimes m}=\ell^2(\mathbb N^m)$ the Fock space of $m$ bosonic modes with basis $|u\rangle$, $u\in\mathbb N^m$, $D(\vec\mu)=\exp(\vec\mu\cdot\vec a^\dagger-\vec a\cdot\vec\mu^\dagger)$ the multi-mode displacement, and
--   $$\mathcal N_n^{\otimes m}(\rho)=\int d^2\vec\mu\;P_n(\vec\mu)\,D(\vec\mu)\,\rho\,D^\dagger(\vec\mu),\qquad P_n(\vec\mu)=\frac{e^{-|\vec\mu|^2/n}}{(\pi n)^m},$$
--   the $m$-use classical-noise channel ($P_n$ is the point mass at $0$ when $n=0$, so $\mathcal N_0^{\otimes m}$ is the identity). For an operator $A$ and $z\ge1$, $\|A\|_z=(\operatorname{Tr}|A|^z)^{1/z}\in[0,\infty]$.
--
--   Let $k\ge1$ be an integer and $\psi\in\mathcal H^{\otimes m}$ a unit vector, $\rho=|\psi\rangle\langle\psi|$. Then the function $(\vec\mu_1,\dots,\vec\mu_k)\mapsto\prod_{s=1}^k\langle\psi|D^\dagger(\vec\mu_s)D(\vec\mu_{s+1})|\psi\rangle$ (with $\vec\mu_{k+1}=\vec\mu_1$) is integrable for $P_n(\vec\mu_1)\cdots P_n(\vec\mu_k)\,d^2\vec\mu_1\cdots d^2\vec\mu_k$, its integral $J$ is a nonnegative real number, and
--   $$\operatorname{Tr}\big\{[\mathcal N_n^{\otimes m}(\rho)]^k\big\}=J=\int d^2\vec\mu_1\cdots d^2\vec\mu_k\,P_n(\vec\mu_1)\cdots P_n(\vec\mu_k)\,\langle\psi|D^\dagger(\vec\mu_1)D(\vec\mu_2)|\psi\rangle\cdots\langle\psi|D^\dagger(\vec\mu_k)D(\vec\mu_1)|\psi\rangle .$$
--
--   This rewrites the $k$-th output moment as an expectation value of the operator $\Theta$ of (21) in the $k$-fold copy $\psi^{\otimes k}$, which is the starting point of the upper bound (12).
--
--   Differences from the source:
--   - reading: ρ in (16), and D†(µ1), D†(µk) printed without arrows → ρ = |ψ⟩⟨ψ| the pure input fixed in Part one; the multi-mode displacements D†(μ⃗_1), D†(μ⃗_k); reason: Sec. I A works with the pure input from Part one on; the arrows are restored as in (17)
--   - encoding: Tr{[N(ρ)]^k} → Σ_u ⟨u|(A†A)^{k/2}|u⟩ for the output A, in [0, ∞]; reason: A is positive, so (A†A)^{k/2} = A^k
--   - encoding: N_n^{⊗m} as an operator on H^{⊗m} with the integral (14) → the integral (14) on Fock coefficient arrays over ℓ²(ℕ^m), P_n as the law of independent N(0, n/2) real and imaginary parts (Dirac mass at n = 0); reason: Mathlib has no Hilbert tensor product; ℓ²(ℕ)^{⊗m} = ℓ²(ℕ^m) and the same channel on every input
--   - encoding: Tr{[N(ρ)]^k} = ∫ … (an identity of a nonnegative number with a Gaussian average) → the integrand is integrable, the integral has imaginary part 0 and real part ≥ 0, and Tr{[N(ρ)]^k} = its real part; reason: the trace lives in [0, ∞] and the integral in ℂ; a non-integrable integrand would have the junk integral 0
-- source:
--   Giovannetti & Lloyd, Additivity properties of a Gaussian channel, arXiv:quant-ph/0403075v3, p. 3, eqs. (16)–(17)

import Mathlib
import Definitions.Def_GaussAddit_Noise_Channel

open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity rankOne)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace GaussAddit.Noise

theorem eq_16_17 (n : ℝ) (hn : 0 ≤ n) (m k : ℕ) (hk : 1 ≤ k) (ψ : Hilbert (Occ m))
    (hψ : ‖ψ‖ = 1) :
    Integrable (fun μ : Fin k → Fin m → ℂ => ∏ s, overlap ψ (μ s) (μ (finRotate k s)))
        (Measure.pi fun _ : Fin k => noiseLaw n m) ∧
      (∫ μ, ∏ s, overlap ψ (μ s) (μ (finRotate k s))
          ∂(Measure.pi fun _ : Fin k => noiseLaw n m)).im = 0 ∧
      0 ≤ (∫ μ, ∏ s, overlap ψ (μ s) (μ (finRotate k s))
          ∂(Measure.pi fun _ : Fin k => noiseLaw n m)).re ∧
      tracePow k (channel n m (rankOne ψ)) =
        ENNReal.ofReal (∫ μ, ∏ s, overlap ψ (μ s) (μ (finRotate k s))
          ∂(Measure.pi fun _ : Fin k => noiseLaw n m)).re := by sorry

end GaussAddit.Noise
