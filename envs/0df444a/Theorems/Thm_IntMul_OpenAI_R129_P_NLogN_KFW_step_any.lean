-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFW_step_any
-- name    : IntMul.OpenAI.R129.P.NLogN.KFW.step_any
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:31.555905+00:00
-- url     : https://prove2.me/theorems/4931d6a6-e396-4bd7-8005-8a93ec607350
-- title:
--   Every step of a node (κ = 2⁻¹²⁹ constants)
-- statement:
--   **Every step of a node**, at the `same-network-129` constants.
--
--   This is `NLogN.KFW.step_any` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFW: the steps of a node of the uniform level procedure*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFW.step_any` (https://prove2.me/theorems/01bbb4d9-f6f1-48ba-8dde-4b930304e959).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open _root_.NLogN hiding padL vE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFW hiding RowU RowUP cBody cCL cChain cLowP cLowPart cTot cbW clF coefF
open _root_.IntMul.OpenAI.R129.P.NLogN.KFW
open Complex
open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR FrOK St aE bodyU cBody fIn kS negP outR pT padL rowR stD
open _root_.NLogN.KFD hiding levF scr
open _root_.NLogN.KFB hiding permL permP
open _root_.NLogN.KFG hiding cTbl imE reE xD
open _root_.NLogN.KFH
open _root_.NLogN.KFN hiding pcs phStepC τ50
open _root_.IntMul.OpenAI.R129.P.NLogN.KFN
open _root_.Butterfly hiding Op
variable {Pp : ℕ} {Isym : List Sym} {tbl : Fin Pp → IStmt HS Pp}
variable {σ : Fin HS → Option ℤ} {K t S0 r H Z k e B Bn : ℕ}

open _root_.NLogN hiding padL vE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFW hiding RowU RowUP cBody cCL cChain cLowP cLowPart cTot cbW clF coefF
open _root_.IntMul.OpenAI.R129.P.NLogN.KFW

theorem IntMul.OpenAI.R129.P.NLogN.KFW.step_any {rowC : IStmt HS Pp} {Kc : ℝ} (hRow : RowU Isym tbl rowC Kc) (hKc : 0 ≤ Kc)
    {jL : Fin Pp} (hj : tbl jL = levC jL rowC)
    (hN : NodeR σ K t S0 r H k e B Bn) (hB : B = P8Lift.Wc * Bn)
    (hK6 : 6 ≤ K) (hr : 1 ≤ r) (hKZ : 80 * Z * (Z + 2) ≤ 2 ^ K) (Zr : ℕ) (hZZ : Z ≤ Zr) (hZr : Zr + 2 ≤ r)
    (hHZ : H + 1 < 2 ^ Z) (hS : 1 ≤ S0) (hBn : 1 ≤ Bn)
    (hKe : K * (mC ^ (k + 1) - 1) ≤ e) (het : e - e % K + K ≤ t)
    (hz16 : zsz ((16 * (B * 2 ^ t * S0 * r) : ℕ) : ℤ) ≤ Z)
    (hV : zsz ((Vb K t S0 r H (k + 1) B : ℕ) : ℤ) ≤ Zr) (cI : ℕ)
    (IH : ∀ h : Fin mC, SImplQ Isym tbl (fun s => Agree (σChild σ K k e Bn h) s) 0 H r
      (fun c : Fin (mC ^ k) => 2 ^ ((e - h.val * (K * mC ^ k)) - K * c.val) * S0) (nN Bn t S0)
      (Butterfly.tens Cm) (levC jL rowC) (ES k) (DWb Lc P8Lift.sc P8Lift.Wc NLogN.KFW.A0 k) (fun _ => cI))
    (a : P8Lift.RStep (Fin P8Lift.Wc) mC) (ha : a ∈ P8Lift.complexIface.net) :
    ∃ (dw c : ℕ), RImplQ Isym tbl (fun s => Agree σ s) 0 H r (nN Bn t S0) (stN K e k S0)
        (a.den (Butterfly.tens Cm)) (stepC jL rowC a) (eSt k a) dw (fun _ => c) ∧
      dw ≤ (if a.isChild then DWb Lc P8Lift.sc P8Lift.Wc NLogN.KFW.A0 k + (Eb Lc P8Lift.sc k + 2) * P8Lift.Wc
        else dwloc P8Lift.Wc NLogN.KFW.A0) ∧
      (c : ℝ) ≤ (if a.isChild then (cI : ℝ) else 0) +
        ((Mloc : ℝ) + 18 * (Kc * (K + 2) + 1) * ((mC : ℝ) ^ k + 1) ^ τ50) *
          ((P8Lift.Wc * nN Bn t S0 * Yu r Zr H : ℕ) : ℝ) := by sorry
