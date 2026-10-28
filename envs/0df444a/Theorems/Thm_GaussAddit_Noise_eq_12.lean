-- Prove2me | Theorems.Thm_GaussAddit_Noise_eq_12
-- name    : GaussAddit.Noise.eq_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:48.22199+00:00
-- url     : https://prove2.me/theorems/3f78b5f2-a19d-4c74-8f1f-28d2cbb48af8
-- title:
--   Eq. (12) — Tr{[N_n^{⊗m}(ρ)]^k} ≤ [(n+1)^k − n^k]^(−m) for every input state ρ of the m uses (reading: z printed for k)
-- statement:
--   Throughout, $n\ge 0$ is the noise parameter, $m\ge 0$ the number of channel uses, $\mathcal H^{\otimes m}=\ell^2(\mathbb N^m)$ the Fock space of $m$ bosonic modes with basis $|u\rangle$, $u\in\mathbb N^m$, $D(\vec\mu)=\exp(\vec\mu\cdot\vec a^\dagger-\vec a\cdot\vec\mu^\dagger)$ the multi-mode displacement, and
--   $$\mathcal N_n^{\otimes m}(\rho)=\int d^2\vec\mu\;P_n(\vec\mu)\,D(\vec\mu)\,\rho\,D^\dagger(\vec\mu),\qquad P_n(\vec\mu)=\frac{e^{-|\vec\mu|^2/n}}{(\pi n)^m},$$
--   the $m$-use classical-noise channel ($P_n$ is the point mass at $0$ when $n=0$, so $\mathcal N_0^{\otimes m}$ is the identity). For an operator $A$ and $z\ge1$, $\|A\|_z=(\operatorname{Tr}|A|^z)^{1/z}\in[0,\infty]$.
--
--   Let $k\ge1$ be an integer. For every density operator $\rho$ of the $m$ uses, entangled ones included,
--   $$\operatorname{Tr}\big\{[\mathcal N_n^{\otimes m}(\rho)]^k\big\}\le\left[\frac{1}{(n+1)^k-n^k}\right]^m .$$
--
--   This is the upper bound that, with the coherent-state value (10), proves the paper's main identity (11).
--
--   Differences from the source:
--   - reading: right-hand side [1/((n + 1)^z − n^z)]^m with z unbound → [1/((n + 1)^k − n^k)]^m with the integer k of the left-hand side; reason: z is not bound in (12); k is the only reading consistent with (11), (22) and (34)
--   - encoding: Tr{[N(ρ)]^k} → Σ_u ⟨u|(A†A)^{k/2}|u⟩ for the output A, in [0, ∞]; reason: A is positive, so (A†A)^{k/2} = A^k
--   - encoding: N_n^{⊗m} as an operator on H^{⊗m} with the integral (14) → the integral (14) on Fock coefficient arrays over ℓ²(ℕ^m), P_n as the law of independent N(0, n/2) real and imaginary parts (Dirac mass at n = 0); reason: Mathlib has no Hilbert tensor product; ℓ²(ℕ)^{⊗m} = ℓ²(ℕ^m) and the same channel on every input
-- source:
--   Giovannetti & Lloyd, Additivity properties of a Gaussian channel, arXiv:quant-ph/0403075v3, p. 2, eq. (12)

import Mathlib
import Definitions.Def_GaussAddit_Noise_Channel

open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity rankOne)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace GaussAddit.Noise

theorem eq_12 (n : ℝ) (hn : 0 ≤ n) (m k : ℕ) (hk : 1 ≤ k) (ρ : State (Occ m)) :
    tracePow k (channel n m ρ.coefficients) ≤
      ENNReal.ofReal (((n + 1) ^ k - n ^ k)⁻¹ ^ m) := by sorry

end GaussAddit.Noise
