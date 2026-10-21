-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFW_stepQ_row
-- name    : IntMul.OpenAI.R129.P.NLogN.KFW.stepQ_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:27.689781+00:00
-- url     : https://prove2.me/theorems/2d0f0c1e-d39f-44b4-a75c-a13587d9c14c
-- title:
--   A row addition on the node roles (κ = 2⁻¹²⁹ constants)
-- statement:
--   **A row addition on the node roles**, at the `same-network-129` constants.
--
--   This is `NLogN.KFW.stepQ_row` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFW: pushes of fresh frames, and the uniform row-addition step*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFW.stepQ_row` (https://prove2.me/theorems/49b53e80-cb5e-466d-822c-f085230886a4).

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
variable {Pp : ℕ} {Isym : List Sym} {tbl : Fin Pp → IStmt HS Pp} {Q : IState HS → Prop}
  {lo hi : ℕ}
variable {σ : Fin HS → Option ℤ} {K t S0 r H k e B Bn : ℕ}

open _root_.NLogN hiding padL vE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFW hiding RowU RowUP cBody cCL cChain cLowP cLowPart cTot cbW clF coefF
open _root_.IntMul.OpenAI.R129.P.NLogN.KFW

theorem IntMul.OpenAI.R129.P.NLogN.KFW.stepQ_row {rowC : IStmt HS Pp} {Kc : ℝ} (hRow : RowU Isym tbl rowC Kc)
    (hN : NodeR σ K t S0 r H k e B Bn) (hQ : ∀ s, Q s → Agree σ s) (hhi : hi ≤ H)
    (hK6 : 6 ≤ K) (hr : 1 ≤ r) (Z : ℕ) (hKZ : 80 * Z * (Z + 2) ≤ 2 ^ K) (hS : 1 ≤ S0)
    (hBn : 1 ≤ Bn) (hKe : K * (mC ^ (k + 1) - 1) ≤ e) (het : e - e % K + K ≤ t)
    (hZ : zsz ((16 * (P8Lift.Wc * (nN Bn t S0 * r)) : ℕ) : ℤ) ≤ Z) (Bz : ℕ)
    (hBz : zsz ((mC ^ k + K + e + t + S0 + Bn + r + H + mC : ℕ) : ℤ) ≤ Bz)
    (w : Fin P8Lift.Wc) (i j : Fin mC) (hij : i ≠ j) :
    ∃ cost : ℕ → ℕ,
      RImplQ Isym tbl Q lo hi r (nN Bn t S0) (stN K e k S0)
        ((P8Lift.RStep.rowAdd w i j hij : P8Lift.RStep (Fin P8Lift.Wc) mC).den
          (Butterfly.tens Cm : Butterfly.Op (Fin (mC ^ k))))
        (wrapQ P8Lift.Wc w.val wL NLogN.KFW.w1 (withPushI (rowPush i j) rowC)) 0 (0 + (0 + 2) * P8Lift.Wc)
        (cWrapQ P8Lift.Wc (nN Bn t S0 * r) Z 0 0
          (fun x => cFrame 10 1 Bz + cost x + (10 * (2 * Bz + 2) + 1))) ∧
      ∀ x, x ≤ H → (cost x : ℝ) ≤ (Kc * (K + 2) + 1) * ((nN Bn t S0 : ℕ) : ℝ) *
        ((r : ℝ) * (H + 1) * ((mC : ℝ) ^ k + 1) ^ τ50 + (KFR.PsiR r Z H : ℝ)) := by sorry
