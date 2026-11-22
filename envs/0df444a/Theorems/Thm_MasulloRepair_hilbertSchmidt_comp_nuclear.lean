-- Prove2me | Theorems.Thm_MasulloRepair_hilbertSchmidt_comp_nuclear
-- name    : MasulloRepair.hilbertSchmidt_comp_nuclear
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-21T20:06:00.762158+00:00
-- url     : https://prove2.me/theorems/43146fc7-7b5f-49db-b091-ff212a7c45d7
-- title:
--   Two Hilbert–Schmidt operators give a nuclear composition with a trace-norm bound
-- statement:
--   Let $H$ be a complete separable complex Hilbert space, and let $A,B:H\to H$ be Hilbert–Schmidt operators. Their composition is nuclear, and
--   $$\|AB\|_{\mathrm{Tr}}\le\|A\|_{S_2}\,\|B\|_{S_2}.$$
--   Here nuclearity, the trace norm, and the Hilbert–Schmidt norms are the existing Hilbert-space definitions in the mission. In particular the trace norm is the basis-defined trace of $\sqrt{T^*T}$.
--
--   This supplies the factorization step that turns two square-integrable kernel estimates into a trace-class estimate. Neither factor nor their product is assumed nuclear.
-- source:
--   Auxiliary smoothing theorem for Yi's 'Exact spatial distribution of the prime atom, and a test of reciprocal inversion as a repair of (11.3.2.4)', https://prove2.me/missions/638f9b7f-e232-4624-ba08-5889465bb1e7#comment-26b2fce9-9b7f-4e53-be0e-981993a5ae05, paragraph 'Why the actual compact-window limit has an explicit kernel here': the nuclearity of compactly restricted convolution by Fourier factorization. Also supports step 4 of the fixed-prime calculation, https://prove2.me/missions/638f9b7f-e232-4624-ba08-5889465bb1e7#comment-a91427c0-0f6d-4e33-aa30-fe6dd8cddd02. This is an unconditional analytic ingredient of the proposed repair; none of the source's arithmetic range or zero-free assertions is an assumption or conclusion here. Trace-norm input: https://prove2.me/theorems/885ae79f-e5bf-48b3-b708-c38c8abfcd9b. Basis arguments adapted from accepted submission 6bbec8a8-12d8-421e-9b7e-56b5183db337 for https://prove2.me/theorems/e0fc0030-2d95-4de0-ac98-dfbb4ee64cb8.

import Definitions.Def_MasulloGRH_HilbertNuclear
import Mathlib.Analysis.InnerProductSpace.Adjoint
set_option autoImplicit false
open MasulloGRH ContinuousLinearMap

theorem MasulloRepair.hilbertSchmidt_comp_nuclear {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (A B : H →L[ℂ] H) (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) :
    IsNuclearOperator (A ∘L B) ∧
      traceNorm (A ∘L B) ≤ hilbertSchmidtNorm A * hilbertSchmidtNorm B := by sorry
