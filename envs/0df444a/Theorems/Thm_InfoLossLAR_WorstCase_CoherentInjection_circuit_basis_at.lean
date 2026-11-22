-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_CoherentInjection_circuit_basis_at
-- name    : InfoLossLAR.WorstCase.CoherentInjection.circuit_basis_at
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T06:02:07.791533+00:00
-- url     : https://prove2.me/theorems/5ae1f77c-87c0-44df-922b-50945d2cffae
-- title:
--   Reversible implementation of an injective classical string map on basis states
-- statement:
--   Let $P$ compute a binary string map $f$ and $Q$ compute $g$. Fix an input length $n$. For any word $x$ of length $n$ for which $g$ recovers $x$ from the padded encoding of $f(x)$, the combined reversible circuit maps the basis state containing $x$ and blank output to the basis state containing $f(x)$ and blank input. Its work registers are restored to zero. The same circuit works for every eligible word of that length, so the basis identity also determines its effect on their coherent superpositions.
-- source:
--   InfoLossLAR formalization of physical Fourier sampling from a shared bounded-distance decoder. https://prove2.me/theorems/d106aba4-0ad7-4239-9c6b-4a9dc8c9ebc4

import Definitions.Def_InfoLossLAR_ReversibleStringInjection
set_option autoImplicit false
open QAlgorithms QAlgorithms.Complexity
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open InfoLossLAR.WorstCase.CoherentComputeUncompute OAI.MetricKMedian.Binary

namespace InfoLossLAR.WorstCase.CoherentInjection
theorem circuit_basis_at {f g : Str → Str} (P : PolyProgram id id f) (Q : PolyProgram id id g)
    (n : ℕ) (word : Str) (hlen : word.length = n)
    (hinverse : g (CoherentClassicalOracle.paddedOutput P word) = word) :
    runLayered (circuit P Q n) (basis (inputBitsAt P Q n word)) = basis (finalBitsAt P Q n word) := by sorry
end InfoLossLAR.WorstCase.CoherentInjection
