-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFV_xchC_run
-- name    : IntMul.OpenAI.R129.P.NLogN.KFV.xchC_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:10.924466+00:00
-- url     : https://prove2.me/theorems/3071799c-a731-4a2b-9719-6bcb945eecd1
-- title:
--   One exchange on the stored records (κ = 2⁻¹²⁹ constants)
-- statement:
--   **One exchange on the stored records**, at the `same-network-129` constants.
--
--   This is `NLogN.KFV.xchC_run` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFV §33: the chunk exchange as fixed IL code*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFV.xchC_run` (https://prove2.me/theorems/5a88d300-0921-4d9e-b945-53cb1ed01d49).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open _root_.NLogN hiding posE tE twA twB vE zX
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFV hiding Cost18 EwB18 Log18Need P14Need P14Uat Par18Need SwOK cBody3 cBody3R cChunk cLayIn cLayOut cPh3 cPh3R cXch total18
open _root_.IntMul.OpenAI.R129.P.NLogN.KFV
open _root_.IntMul
open _root_.NLogN.RS
open _root_.NLogN.KIL hiding Cfg FR St aE cBr cFwd cStep kG negP outR padL pre2 srcT swF yB
open _root_.NLogN.KFD
open _root_.NLogN.KFB hiding blk permL permP
open _root_.NLogN.KFH hiding gD
open _root_.NLogN.KFC hiding dbl enc encF mvB sT
open _root_.NLogN.KFT hiding tE
open _root_.Synth
open _root_.AModel hiding blk hdPos
open _root_.AModelL12
variable {Pp : ℕ} {I : List Sym} {iprog : Fin Pp → IStmt HS Pp}
set_option maxHeartbeats 1000000

open _root_.NLogN hiding posE tE twA twB vE zX
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFV hiding Cost18 EwB18 Log18Need P14Need P14Uat Par18Need SwOK cBody3 cBody3R cChunk cLayIn cLayOut cPh3 cPh3R cXch total18
open _root_.IntMul.OpenAI.R129.P.NLogN.KFV

theorem IntMul.OpenAI.R129.P.NLogN.KFV.xchC_run {eSw : Fin Pp} {dW : Fin HS} {Kc : ℝ} (HSw : SwOK I iprog eSw dW Kc)
    (hd0 : dW ≠ 0) (hd56 : dW.val < 56) (hKc : 0 ≤ Kc)
    (S : IState HS) (zs : List GI) (l : List ℤ) {i j K n ℓ W B : ℕ}
    (hij : i + K ≤ j) (hj : j + K ≤ n) (hK : 1 ≤ K)
    (hzs : zs.length = 2 ^ n * 2 ^ ℓ) (hgb : NLogN.KFB.GB W zs)
    {eE eK eM eI eW : Ex HS} (sE : DSafe dW eE) (sK : DSafe dW eK) (sM : DSafe dW eM)
    (sI : DSafe dW eI) (sW : DSafe dW eW)
    (vE : EV (encK S (o0 (gflat zs ++ l))) B eE ((n - j - K + ℓ : ℕ) : ℤ))
    (vK : EV (encK S (o0 (gflat zs ++ l))) B eK (K : ℤ))
    (vM : EV (encK S (o0 (gflat zs ++ l))) B eM ((j - i - K : ℕ) : ℤ))
    (vI : EV (encK S (o0 (gflat zs ++ l))) B eI (i : ℤ))
    (vW : EV (encK S (o0 (gflat zs ++ l))) B eW (W : ℤ))
    (hB : n + ℓ + 5 ≤ B) (hWB : W ≤ B) :
    IRuns I iprog (xchC eSw dW eE eK eM eI eW) (encK S (o0 (gflat zs ++ l)))
      (encK S (o0 (gflat (zMv n (2 ^ ℓ) (bsIdx i j K) zs) ++ l)))
      (cXch Kc eE eK eM eI eW n ℓ K W B) := by sorry
