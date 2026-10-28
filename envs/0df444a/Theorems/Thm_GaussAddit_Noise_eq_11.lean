-- Prove2me | Theorems.Thm_GaussAddit_Noise_eq_11
-- name    : GaussAddit.Noise.eq_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:49.112991+00:00
-- url     : https://prove2.me/theorems/1407cd6e-bc0d-4bae-b69f-2ca46284123a
-- title:
--   Eq. (11) — ν_k(N_n^{⊗m}) = [(n+1)^k − n^k]^(−m/k) for every integer k ≥ 1, attained by every coherent product |α_1⟩ ⊗ ⋯ ⊗ |α_m⟩
-- statement:
--   Throughout, $n\ge 0$ is the noise parameter, $m\ge 0$ the number of channel uses, $\mathcal H^{\otimes m}=\ell^2(\mathbb N^m)$ the Fock space of $m$ bosonic modes with basis $|u\rangle$, $u\in\mathbb N^m$, $D(\vec\mu)=\exp(\vec\mu\cdot\vec a^\dagger-\vec a\cdot\vec\mu^\dagger)$ the multi-mode displacement, and
--   $$\mathcal N_n^{\otimes m}(\rho)=\int d^2\vec\mu\;P_n(\vec\mu)\,D(\vec\mu)\,\rho\,D^\dagger(\vec\mu),\qquad P_n(\vec\mu)=\frac{e^{-|\vec\mu|^2/n}}{(\pi n)^m},$$
--   the $m$-use classical-noise channel ($P_n$ is the point mass at $0$ when $n=0$, so $\mathcal N_0^{\otimes m}$ is the identity). For an operator $A$ and $z\ge1$, $\|A\|_z=(\operatorname{Tr}|A|^z)^{1/z}\in[0,\infty]$.
--
--   Let $k\ge1$ be an integer. Then:
--
--   1. the maximal output $k$-norm of $m$ uses of the channel is
--   $$\nu_k(\mathcal N_n^{\otimes m})=\sup_\rho\big\|\mathcal N_n^{\otimes m}(\rho)\big\|_k=\left[\frac{1}{(n+1)^k-n^k}\right]^{m/k},$$
--   the supremum running over all density operators $\rho$ of the $m$ uses, entangled ones included;
--   2. the supremum is attained by every coherent product: for every $\vec\alpha\in\mathbb C^m$ the state $|\alpha_1\rangle_1\otimes\cdots\otimes|\alpha_m\rangle_m$ is a density operator whose output has $k$-norm equal to this value.
--
--   Since $\nu_k(\mathcal N_n)=[(n+1)^k-n^k]^{-1/k}$, the identity says $\nu_k(\mathcal N_n^{\otimes m})=[\nu_k(\mathcal N_n)]^m$: the Amosov–Holevo–Werner multiplicativity conjecture (2) holds for this channel at every integer order, and entangled inputs do not help. Equivalently, the minimum output Rényi entropy of integer order $k\ge2$ is additive for $\mathcal N_n$.
--
--   Differences from the source:
--   - generalization: m successive uses (m ⩾ 1) → every m ∈ ℕ, including m = 0; reason: at m = 0 the space is one-dimensional and both sides are 1; specializes to m ⩾ 1
--   - encoding: 'for all integer k' → every integer k ⩾ 1; reason: the z-norm (3) is defined for z ⩾ 1
--   - encoding: max over ρ ∈ H^{⊗m} → supremum over all density operators in [0, ∞], with attainment stated as clause 2; reason: no real default value for an unbounded supremum; clause 2 makes it a maximum
--   - encoding: N_n^{⊗m} as an operator on H^{⊗m} with the integral (14) → the integral (14) on Fock coefficient arrays over ℓ²(ℕ^m), P_n as the law of independent N(0, n/2) real and imaginary parts (Dirac mass at n = 0); reason: Mathlib has no Hilbert tensor product; ℓ²(ℕ)^{⊗m} = ℓ²(ℕ^m) and the same channel on every input
--   - encoding: ‖A‖_z = (Tr|A|^z)^{1/z}, a real number → (Σ_u ⟨u|(A†A)^{z/2}|u⟩)^{1/z} by the continuous functional calculus, valued in [0, ∞]; reason: |A| = (A†A)^{1/2}; the Fock-basis trace of a positive operator is basis independent; [0, ∞] has no junk value
-- source:
--   Giovannetti & Lloyd, Additivity properties of a Gaussian channel, arXiv:quant-ph/0403075v3, p. 2, eq. (11) and the sentence after it; proof Sec. I A (pp. 2–4), Sec. I B (pp. 4–5), App. A (pp. 7–8)

import Mathlib
import Definitions.Def_GaussAddit_Noise_Channel

open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity rankOne)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace GaussAddit.Noise

theorem eq_11 (n : ℝ) (hn : 0 ≤ n) (m k : ℕ) (hk : 1 ≤ k) :
    nu k n m = ENNReal.ofReal (((n + 1) ^ k - n ^ k) ^ (-(m : ℝ) / k)) ∧
      ∀ α : Fin m → ℂ, ∃ ρ : State (Occ m), ρ.coefficients = coherentArr α ∧
        zNorm k (channel n m ρ.coefficients) =
          ENNReal.ofReal (((n + 1) ^ k - n ^ k) ^ (-(m : ℝ) / k)) := by sorry

end GaussAddit.Noise
