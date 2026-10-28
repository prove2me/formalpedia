-- Prove2me | Theorems.Thm_GaussAddit_Noise_part_one
-- name    : GaussAddit.Noise.part_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:42.97152+00:00
-- url     : https://prove2.me/theorems/09fab6e1-1644-4692-ad59-1c9a616abef1
-- title:
--   Sec. I A, Part one — pure inputs suffice: every input is dominated by a pure input, and ν_z(N_n^{⊗m}) is the supremum over pure states
-- statement:
--   Throughout, $n\ge 0$ is the noise parameter, $m\ge 0$ the number of channel uses, $\mathcal H^{\otimes m}=\ell^2(\mathbb N^m)$ the Fock space of $m$ bosonic modes with basis $|u\rangle$, $u\in\mathbb N^m$, $D(\vec\mu)=\exp(\vec\mu\cdot\vec a^\dagger-\vec a\cdot\vec\mu^\dagger)$ the multi-mode displacement, and
--   $$\mathcal N_n^{\otimes m}(\rho)=\int d^2\vec\mu\;P_n(\vec\mu)\,D(\vec\mu)\,\rho\,D^\dagger(\vec\mu),\qquad P_n(\vec\mu)=\frac{e^{-|\vec\mu|^2/n}}{(\pi n)^m},$$
--   the $m$-use classical-noise channel ($P_n$ is the point mass at $0$ when $n=0$, so $\mathcal N_0^{\otimes m}$ is the identity). For an operator $A$ and $z\ge1$, $\|A\|_z=(\operatorname{Tr}|A|^z)^{1/z}\in[0,\infty]$.
--
--   Let $z\ge1$. For every density operator $\rho$ of the $m$ uses there is a unit vector $\psi\in\mathcal H^{\otimes m}$ with
--   $$\big\|\mathcal N_n^{\otimes m}(\rho)\big\|_z\le\big\|\mathcal N_n^{\otimes m}(|\psi\rangle\langle\psi|)\big\|_z ,$$
--   and consequently
--   $$\nu_z(\mathcal N_n^{\otimes m})=\sup_{\|\psi\|=1}\big\|\mathcal N_n^{\otimes m}(|\psi\rangle\langle\psi|)\big\|_z .$$
--
--   This is the reduction "without loss of generality the input is pure" that opens the proof of (11): an upper bound proved for pure inputs holds for all inputs.
--
--   Differences from the source:
--   - reading: 'the maximization in Eq. (2) is achievable with pure input states' → every input's output z-norm is dominated by that of some pure input, and the supremum over all states equals the supremum over unit vectors; reason: the two forms of 'achievable' (pointwise domination and equality of the optimal values); both are stated
--   - encoding: N_n^{⊗m} as an operator on H^{⊗m} with the integral (14) → the integral (14) on Fock coefficient arrays over ℓ²(ℕ^m), P_n as the law of independent N(0, n/2) real and imaginary parts (Dirac mass at n = 0); reason: Mathlib has no Hilbert tensor product; ℓ²(ℕ)^{⊗m} = ℓ²(ℕ^m) and the same channel on every input
--   - encoding: ‖A‖_z = (Tr|A|^z)^{1/z}, a real number → (Σ_u ⟨u|(A†A)^{z/2}|u⟩)^{1/z} by the continuous functional calculus, valued in [0, ∞]; reason: |A| = (A†A)^{1/2}; the Fock-basis trace of a positive operator is basis independent; [0, ∞] has no junk value
-- source:
--   Giovannetti & Lloyd, Additivity properties of a Gaussian channel, arXiv:quant-ph/0403075v3, p. 2, Sec. I A, Part one

import Mathlib
import Definitions.Def_GaussAddit_Noise_Channel

open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity rankOne)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace GaussAddit.Noise

theorem part_one (z : ℝ) (hz : 1 ≤ z) (n : ℝ) (hn : 0 ≤ n) (m : ℕ) :
    (∀ ρ : State (Occ m), ∃ ψ : Hilbert (Occ m), ‖ψ‖ = 1 ∧
      zNorm z (channel n m ρ.coefficients) ≤ zNorm z (channel n m (rankOne ψ))) ∧
    nu z n m = ⨆ ψ : {ψ : Hilbert (Occ m) // ‖ψ‖ = 1}, zNorm z (channel n m (rankOne ψ.1)) := by sorry

end GaussAddit.Noise
