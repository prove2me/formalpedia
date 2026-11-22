-- Prove2me | Theorems.Thm_MasulloRepair_L2_kernel_composition_nuclear
-- name    : MasulloRepair.L2_kernel_composition_nuclear
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-21T20:06:03.43897+00:00
-- url     : https://prove2.me/theorems/90909276-f243-4a4a-9c1e-ec43c5e0fa06
-- title:
--   Composition of square-integrable kernels is nuclear with a quantitative bound
-- statement:
--   Let $X$ be a second-countable locally compact Hausdorff space with a regular, $\sigma$-finite Borel measure $\mu$. Let $k,l\in L^2(X\times X,\mu\otimes\mu)$ be complex kernels.
--
--   There exists a bounded nuclear operator $T$ on $L^2(X,\mu)$ such that for every $u\in L^2(X,\mu)$, almost everywhere in $x$,
--   $$Tu(x)=\int_X k(x,z)\left(\int_X l(z,y)u(y)\,d\mu(y)\right)d\mu(z),$$
--   and
--   $$\|T\|_{\mathrm{Tr}}\le\|k\|_{L^2(X\times X)}\,\|l\|_{L^2(X\times X)}.$$
--
--   The iterated integral specifies the actual action of the operator. This is a usable trace-class criterion for smoothing constructions: it requires square-integrability of two explicit kernels, without a prior nuclearity assumption or a pointwise diagonal-trace assumption.
-- source:
--   Auxiliary smoothing theorem for Yi's 'Exact spatial distribution of the prime atom, and a test of reciprocal inversion as a repair of (11.3.2.4)', https://prove2.me/missions/638f9b7f-e232-4624-ba08-5889465bb1e7#comment-26b2fce9-9b7f-4e53-be0e-981993a5ae05, paragraph 'Why the actual compact-window limit has an explicit kernel here': the nuclearity of compactly restricted convolution by Fourier factorization. Also supports step 4 of the fixed-prime calculation, https://prove2.me/missions/638f9b7f-e232-4624-ba08-5889465bb1e7#comment-a91427c0-0f6d-4e33-aa30-fe6dd8cddd02. This is an unconditional analytic ingredient of the proposed repair; none of the source's arithmetic range or zero-free assertions is an assumption or conclusion here. Integral-kernel input: https://prove2.me/theorems/e0fc0030-2d95-4de0-ac98-dfbb4ee64cb8, the Hilbert–Schmidt part of Theorem C.3.7.1 as formalized. No nuclearity or diagonal conclusion from its conditional part is assumed.

import Definitions.Def_MasulloGRH_HilbertNuclear
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Regular
set_option autoImplicit false
open MasulloGRH MeasureTheory ContinuousLinearMap

theorem MasulloRepair.L2_kernel_composition_nuclear {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [μ.Regular] [SigmaFinite μ] (k l : X → X → ℂ)
    (hk : MemLp (fun p : X × X => k p.1 p.2) 2 (μ.prod μ))
    (hl : MemLp (fun p : X × X => l p.1 p.2) 2 (μ.prod μ)) :
    ∃ T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ,
      (∀ u : Lp ℂ 2 μ, ∀ᵐ x ∂μ,
        T u x = ∫ z, k x z * (∫ y, l z y * u y ∂μ) ∂μ) ∧
      IsNuclearOperator T ∧
      traceNorm T ≤ (eLpNorm (fun p : X × X => k p.1 p.2) 2 (μ.prod μ)).toReal *
        (eLpNorm (fun p : X × X => l p.1 p.2) 2 (μ.prod μ)).toReal := by sorry
