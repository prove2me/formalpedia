-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_PhysicalFourier_oracle_in_serialized_order
-- name    : InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier.oracle_in_serialized_order
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T05:37:55.094356+00:00
-- url     : https://prove2.me/theorems/bb328109-03b5-4fe6-a9b9-e45db11c0649
-- title:
--   Coherent erasure of a serialized decoder answer with a shared sample pool
-- statement:
--   Given a uniform quantum decoder $C$, there exists a uniform quantum family that erases the predicted answer in a register carrying the framed query, its answer and two spectator registers. Fix any finite indexed superposition with amplitudes $v_i$, jointly injective spectator labels, a shared pool and padded queries. Write $u$ and $u_0$ for the corresponding superpositions before and after the correct answer has been erased. For every physical state $w$, the compute, copy and uncompute circuit $V$ satisfies
--   $$\lVert Vw-u_0\rVert_2 \le \lVert w-u\rVert_2+2\sqrt{\sum_i |v_i|^2\Pr[C\text{ fails on query }i]}.$$
--   The guarantee retains both the query and the spectator labels, allowing later coherent Fourier sampling on the same registers.
-- source:
--   Physical Fourier readout theorem used in https://prove2.me/theorems/23174e03-6b1d-4113-b6b9-4dab17fa850a

import Definitions.Def_InfoLossLAR_RegevSearch_PhysicalFourierReadout
import Definitions.Def_InfoLossLAR_RegevSearch_UniformFourierRow
set_option autoImplicit false
open scoped BigOperators Classical
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSearch InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier
open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeGates CoherentComputeUncompute QuantumXorOracle
open PaddedDecoder SharedPoolCoherence

theorem InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier.oracle_in_serialized_order (C : MFamily) (hC : IsMQPT C) :
    ∃ F : MFamily, IsMQPT F ∧ ∃ widths : ∀ l, l ≤ F.outLen l,
    ∀ {n m H K L J : ℕ} (hkl : K ≤ L) (B : Matrix (Fin n) (Fin n) ℤ) (R : ℚ)
    (prec : ℕ) (pool : Fin m → Fin n → ℤ) (I : Type) [Fintype I] [Nonempty I]
    (h : I → Bits H) (j : I → Bits J) (hi : Function.Injective (fun i => (h i,j i)))
    (q : I → Query B R) (v : I → ℂ) (x : I → Bits L)
    (_hx : ∀ i, ∃ pad : Str, List.ofFn (x i) = encS (word prec pool (q i)) ++ pad),
    let d (i : I) := prefixBits K (encVec encI (q i).answer)
    let init := basisEmbedding (emittedBasis (A:=F.anc L) h j hi x d) v
    let goal := basisEmbedding (emittedBasis (A:=F.anc L) h j hi x (fun _ => (0:Bits K))) v
    let U := leftCircuit (m:=H+J) (circuit (F.circ L) (controls F L K (hkl.trans (widths L))))
    let V := relocateCircuit (oraclePerm H K L J (F.anc L+1)).toEmbedding U
    ∀ (actual : QState (H+K+L+J+(F.anc L+1))),
    stateNorm (runLayered V actual-goal) ≤ stateNorm (actual-init)+2*Real.sqrt (failureMass C prec pool q v) := by sorry
