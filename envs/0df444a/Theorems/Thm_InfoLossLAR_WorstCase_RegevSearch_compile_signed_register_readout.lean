-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_compile_signed_register_readout
-- name    : InfoLossLAR.WorstCase.RegevSearch.compile_signed_register_readout
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T05:40:38.652281+00:00
-- url     : https://prove2.me/theorems/1a273f29-31bc-4b79-99e7-b651c135bdb8
-- title:
--   A uniform compiler for measuring a signed output register
-- statement:
--   Let a polynomial-time program assign to a binary input a quantum circuit on $h$ wires, an offset $j$, and an output shape of $n$ signed words of $b$ bits each. The assignment uses the native Hadamard, phase, $T$, bit-flip, and controlled bit-flip instructions. There is a uniform quantum circuit family with a polynomial-time description generator which implements the readout on every correctly encoded circuit with $j+nb\le h$. For any finite set $A$ of integer vectors, its measured probability of decoding a member of $A$ is
--   \[
--    \sum_{x:\,\operatorname{decode}_{n,b,j}(x)\in A}|\langle x\mid U\mid 0^h\rangle|^2.
--   \]
--   With probability one the output contains the canonical vector encoding within the reserved output prefix. Both the dimension and the register widths may depend on the input.
-- source:
--   InfoLossLAR formalization of the signed-register readout used in the shared-pool Fourier sampler. https://prove2.me/theorems/d106aba4-0ad7-4239-9c6b-4a9dc8c9ebc4

import Definitions.Def_InfoLossLAR_RegevSearch_UniformFourierRow
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch
open QAlgorithms QAlgorithms.Complexity GaussianIteration AdaptiveStages
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
theorem compile_signed_register_readout
    (f : Str → (List Unit × List Unit) × ((List Unit × ℕ) × List (ℕ × ℕ × ℕ))) (hf : Poly f) :
    ∃ (G : MFamily) (desc : Str → Str), Poly desc ∧ (∀ n,desc (unary n)=G.encAt n) ∧ IsMQPT G ∧
    ∀ (w : Str) (v : (List Unit × List Unit) × ((List Unit × ℕ) × List (ℕ × ℕ × ℕ))), f w=v →
    ∀ (s : List Unit × List Unit), v.1=s → ∀ off : ℕ, v.2.1.2=off →
    ∀ c : Layered v.2.1.1.length, v.2.2=c.flatten.map (fun g => match g with
      | .h i => (0,i.val,0) | .s i => (1,i.val,0) | .t i => (2,i.val,0)
      | .x i => (3,i.val,0) | .cnot i j _ => (4,i.val,j.val)) →
    off+s.1.length*s.2.length≤v.2.1.1.length →
    (∀ S, (SignedSlot.slot s).length≤S → outputProb G w (SignedSlot.canon s.1.length S)=1) ∧
      ∀ T : Finset (Vec s.1.length),
        finiteMass ((measuredWord G w).map (SignedSlot.decodeWord s.1.length)) T =
        ∑ x, if ∃ z∈T, encVec encI z <+: GridReadout.Axis.encodeSlices (s.1,s.2,(List.ofFn x).drop off)
          then ‖runLayered c (fun y => if y=(fun _=>false) then 1 else 0) x‖^2 else 0 := by sorry
end InfoLossLAR.WorstCase.RegevSearch
