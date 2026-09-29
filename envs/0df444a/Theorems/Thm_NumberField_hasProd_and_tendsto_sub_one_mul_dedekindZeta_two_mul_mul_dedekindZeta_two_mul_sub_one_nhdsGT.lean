-- Prove2me | Theorems.Thm_NumberField_hasProd_and_tendsto_sub_one_mul_dedekindZeta_two_mul_mul_dedekindZeta_two_mul_sub_one_nhdsGT
-- name    : NumberField.hasProd_and_tendsto_sub_one_mul_dedekindZeta_two_mul_mul_dedekindZeta_two_mul_sub_one_nhdsGT
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/afd3ef79-74f7-51be-85d8-acd49c603b29
-- title:
--   Euler product and residue at s=1 of ζ_K(2s)ζ_K(2s-1)
-- statement:
--   Let $K$ be a number field. The theorem asserts two things simultaneously. First, for every real $s>1$, the family indexed by the height-one primes $v$ of the ring of integers $\mathcal{O}_K$ whose $v$-th term is $\bigl(1-N(v)^{-2s}\bigr)^{-1}\bigl(1-N(v)^{-(2s-1)}\bigr)^{-1}$, where $N(v)=$ `Ideal.absNorm v.asIdeal` is the absolute ideal norm of the corresponding prime ideal, viewed as a complex number, and the complex powers have exponents $-(2s)$ and $-(2s-1)$ with $s$ regarded as a complex number, is unconditionally multipliable with product $\zeta_K(2s)\,\zeta_K(2s-1)$, where $\zeta_K$ is `NumberField.dedekindZeta`. Secondly, as the real variable $s$ tends to $1$ from the right (the limit is taken along the filter $\mathcal{N}_{>}(1)$ of neighbourhoods of $1$ within $(1,\infty)$), the function $s\mapsto (s-1)\,\zeta_K(2s)\,\zeta_K(2s-1)$ converges to $\zeta_K(2)\cdot(\rho_K/2)$, where $\rho_K$ is the real number `NumberField.dedekindZeta_residue K`, the residue of $\zeta_K$ at $s=1$, and the quotient $\rho_K/2$ is formed in $\mathbb{R}$ and then regarded as a complex number.
--
--   This is the Euler-product identity and the residue computation for the product $\zeta_K(2s)\zeta_K(2s-1)$, the Dirichlet series that arises as the global zeta function of a quaternion algebra over $K$ evaluated on a standard test function: the simple pole at $s=1$ comes from the factor $\zeta_K(2s-1)$ and contributes $\rho_K/2$, while $\zeta_K(2s)\to\zeta_K(2)$. It feeds the mass/covolume computation for automorphic forms on a quaternion algebra and the companion statement on partial products over cofinite sets of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_hasProd_and_tendsto_sub_one_mul_dedekindZeta_two_mul_mul_dedekindZeta_two_mul_sub_one_nhdsGT.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Filter Topology NumberField IsDedekindDomain

theorem NumberField.hasProd_and_tendsto_sub_one_mul_dedekindZeta_two_mul_mul_dedekindZeta_two_mul_sub_one_nhdsGT
    (K : Type) [Field K] [NumberField K] :
    (∀ s : ℝ, 1 < s →
      HasProd (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
          (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * (s : ℂ))))⁻¹ *
          (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * (s : ℂ) - 1)))⁻¹)
        (NumberField.dedekindZeta K (2 * (s : ℂ)) * NumberField.dedekindZeta K (2 * (s : ℂ) - 1))) ∧
    Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) *
        (NumberField.dedekindZeta K (2 * (s : ℂ)) * NumberField.dedekindZeta K (2 * (s : ℂ) - 1)))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (NumberField.dedekindZeta K 2 * ((NumberField.dedekindZeta_residue K / 2 : ℝ) : ℂ))) := by sorry
