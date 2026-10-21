-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFW_ctot_real
-- name    : IntMul.OpenAI.R129.P.NLogN.KFW.ctot_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:25.815009+00:00
-- url     : https://prove2.me/theorems/b8602a12-d7c2-4e85-bd00-ed008be1f36e
-- title:
--   The real cost bound from the unit bound (κ = 2⁻¹²⁹ constants)
-- statement:
--   **The real cost bound from the unit bound**, at the `same-network-129` constants.
--
--   This is `NLogN.KFW.ctot_real` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFW C-layer 21: the entry procedure with its closed cost*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFW.ctot_real` (https://prove2.me/theorems/6fe0f55f-7e13-4309-b218-640ad97a5363).

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

open _root_.NLogN hiding padL vE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFW hiding RowU RowUP cBody cCL cChain cLowP cLowPart cTot cbW clF coefF
open _root_.IntMul.OpenAI.R129.P.NLogN.KFW

theorem IntMul.OpenAI.R129.P.NLogN.KFW.ctot_real {Kc : ℝ} (hKc : 0 ≤ Kc) {K S r P D w Z : ℕ} (hS : 1 ≤ S) (hP : 1 ≤ P)
    (hD : 1 ≤ D) (hr : 1 ≤ r) (hZr : Z + 32 ≤ r)
    (hwZ : w + KFM.EwB NLogN.KFW.A0 D + 2 < 2 ^ Z) (hK : 1 ≤ K) :
    (cTot Kc K S r (w + KFM.EwB NLogN.KFW.A0 D) P D (Nat.log mC D) (q0f D (Nat.log mC D))
      (padB (P * 2 ^ (K * q0f D (Nat.log mC D))) (P8Lift.Wc ^ Nat.log mC D)) Z (Z + 30) (Z + 5) w : ℝ) ≤
      Mb0 * (coefF (18 * Kc + 18) K D * ((P * 2 ^ (K * D) * S : ℕ) : ℝ) *
        (Xf r (KFR.PsiR r Z) (w + KFM.EwB NLogN.KFW.A0 D) : ℝ)) := by sorry
