-- Prove2me | Theorems.Thm_GaussAddit_Noise_eq_10
-- name    : GaussAddit.Noise.eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:41.143499+00:00
-- url     : https://prove2.me/theorems/2a5cf8bd-e2a1-4824-ba68-12ede51c6df5
-- title:
--   Eq. (10) — coherent inputs: ‖N_n^{⊗m}(|α⃗⟩⟨α⃗|)‖_z = [(n+1)^z − n^z]^(−m/z) for every real z ≥ 1 (posed for m-fold coherent products)
-- statement:
--   Throughout, $n\ge 0$ is the noise parameter, $m\ge 0$ the number of channel uses, $\mathcal H^{\otimes m}=\ell^2(\mathbb N^m)$ the Fock space of $m$ bosonic modes with basis $|u\rangle$, $u\in\mathbb N^m$, $D(\vec\mu)=\exp(\vec\mu\cdot\vec a^\dagger-\vec a\cdot\vec\mu^\dagger)$ the multi-mode displacement, and
--   $$\mathcal N_n^{\otimes m}(\rho)=\int d^2\vec\mu\;P_n(\vec\mu)\,D(\vec\mu)\,\rho\,D^\dagger(\vec\mu),\qquad P_n(\vec\mu)=\frac{e^{-|\vec\mu|^2/n}}{(\pi n)^m},$$
--   the $m$-use classical-noise channel ($P_n$ is the point mass at $0$ when $n=0$, so $\mathcal N_0^{\otimes m}$ is the identity). For an operator $A$ and $z\ge1$, $\|A\|_z=(\operatorname{Tr}|A|^z)^{1/z}\in[0,\infty]$.
--
--   Let $z\ge1$ be real and $\vec\alpha=(\alpha_1,\dots,\alpha_m)\in\mathbb C^m$. Then the coherent product $\rho_{\vec\alpha}=|\alpha_1\rangle\langle\alpha_1|\otimes\cdots\otimes|\alpha_m\rangle\langle\alpha_m|$ is a density operator and
--   $$\big\|\mathcal N_n^{\otimes m}(\rho_{\vec\alpha})\big\|_z=\left[\frac{1}{(n+1)^z-n^z}\right]^{m/z}.$$
--   For $m=1$ this is (10). The value does not depend on $\vec\alpha$.
--
--   It gives the lower bound in the paper's main identity (11) and shows that coherent products attain it.
--
--   Differences from the source:
--   - generalization: a single use (m = 1), ρ_α = |α⟩⟨α| → m-fold coherent products |α_1⟩ ⊗ ⋯ ⊗ |α_m⟩, every m ≥ 0; reason: m = 1 is the printed (10); the m-fold form is the one the proof of (11) uses (p. 2: 'the m uses of the channel have been prepared in coherent states')
--   - generalization: ρ_α taken to be a state → also concludes that the coherent-product array is a density operator; reason: the paper takes this for granted; stating it rules out a vacuous input
--   - encoding: N_n^{⊗m} as an operator on H^{⊗m} with the integral (14) → the integral (14) on Fock coefficient arrays over ℓ²(ℕ^m), P_n as the law of independent N(0, n/2) real and imaginary parts (Dirac mass at n = 0); reason: Mathlib has no Hilbert tensor product; ℓ²(ℕ)^{⊗m} = ℓ²(ℕ^m) and the same channel on every input
--   - encoding: ‖A‖_z = (Tr|A|^z)^{1/z}, a real number → (Σ_u ⟨u|(A†A)^{z/2}|u⟩)^{1/z} by the continuous functional calculus, valued in [0, ∞]; reason: |A| = (A†A)^{1/2}; the Fock-basis trace of a positive operator is basis independent; [0, ∞] has no junk value
-- source:
--   Giovannetti & Lloyd, Additivity properties of a Gaussian channel, arXiv:quant-ph/0403075v3, p. 2, eq. (10)

import Mathlib
import Definitions.Def_GaussAddit_Noise_Channel

open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity rankOne)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace GaussAddit.Noise

theorem eq_10 (n : ℝ) (hn : 0 ≤ n) (m : ℕ) (z : ℝ) (hz : 1 ≤ z) (α : Fin m → ℂ) :
    IsDensity (coherentArr α) ∧
      zNorm z (channel n m (coherentArr α)) =
        ENNReal.ofReal (((n + 1) ^ z - n ^ z) ^ (-(m : ℝ) / z)) := by sorry

end GaussAddit.Noise
