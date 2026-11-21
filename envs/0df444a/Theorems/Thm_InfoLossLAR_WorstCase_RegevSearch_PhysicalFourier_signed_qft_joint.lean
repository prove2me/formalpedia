-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_PhysicalFourier_signed_qft_joint
-- name    : InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier.signed_qft_joint
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T05:38:05.549989+00:00
-- url     : https://prove2.me/theorems/db9c8581-f73e-47c6-bf1d-7f220cd3c327
-- title:
--   Signed quantum Fourier readout in the presence of a reference register
-- statement:
--   Let $B$ be a nonsingular integer lattice basis, $M=2^b$ a dyadic grid and $r>0$ a Gaussian parameter. One uniform choice of synthesis constant works in every dimension. The signed readout of the rowwise quantum Fourier circuit always encodes an integer vector. For any finite event $T$, unit input $u$, independent unit reference state $j$, and unit joint physical state $w$, its probability differs from the finite Gaussian Fourier law on $T$ by at most
--   $$2\lVert w-u\otimes j\rVert_2+2\lVert u-u_{B,r,M}\rVert_2+\frac1{4(k+1)}.$$
--   Here $u_{B,r,M}$ is the ideal finite Gaussian state on the data register and the synthesis precision is chosen for accuracy $k$.
-- source:
--   Physical Fourier readout theorem used in https://prove2.me/theorems/23174e03-6b1d-4113-b6b9-4dab17fa850a

import Definitions.Def_InfoLossLAR_RegevSearch_PhysicalFourierReadout
import Definitions.Def_InfoLossLAR_RegevSearch_UniformFourierRow
set_option autoImplicit false
open scoped BigOperators Classical
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSearch InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier
open QAlgorithms QAlgorithms.Complexity CoherentDecoder ControlledNativeGates
open NativeQFTPlanCompile GridReadout.Axis

theorem InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier.signed_qft_joint : ∃ a : ℕ, 0<a ∧ ∀ (nt : List Unit) (x : Input) (γ : ℕ)
    (B : Matrix (Fin nt.length) (Fin nt.length) ℤ) (hB : B.det≠0) (r : ℝ), 0<r →
    ∀ (k : ℕ), precision nt.length x.1.length k ≤ x.2.length →
    ∀ (v : QState (nt.length*x.1.length+2)) (_hv : stateNorm v=1) (junk : QState γ) (_hj : stateNorm junk=1)
      (actual : QState (nt.length*x.1.length+2+γ)) (_ha : stateNorm actual = 1),
    let G := circuit a x (List.finRange nt.length)
    let u := WithLp.toLp 2 (runLayered (leftCircuit (m:=γ) G) actual)
    let emitted := fun p : Bits (nt.length*x.1.length+2+γ) => encodeSlices (nt,x.1,List.ofFn (leftRegister p : Bits (nt.length*x.1.length+2)))
    let ideal := inputState (dualInput (b:=x.1.length) B hB r)
    bornEvent (fun p => ∃ z : Fin nt.length → ℤ, encVec encI z <+: emitted p) u = 1 ∧
    ∀ T : Finset (Fin nt.length → ℤ),
      |bornEvent (fun p => ∃ z ∈ T, encVec encI z <+: emitted p) u - fourierEvent B r (2^x.1.length) T| ≤
        2*stateNorm (actual-tensorState v junk)+2*stateNorm (v-liftRows ideal.ofLp)+1/(4*((k:ℝ)+1)) := by sorry
