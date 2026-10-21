-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFW_lvQ_all
-- name    : IntMul.OpenAI.R129.P.NLogN.KFW.lvQ_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:06.488088+00:00
-- url     : https://prove2.me/theorems/7e17fadf-39ff-4b16-9924-262422a94c71
-- title:
--   Every level (κ = 2⁻¹²⁹ constants)
-- statement:
--   **Every level**, at the `same-network-129` constants.
--
--   This is `NLogN.KFW.lvQ_all` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFW: the levels of the uniform level procedure*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFW.lvQ_all` (https://prove2.me/theorems/8d530979-ba69-4d52-bd7e-05fa092009eb).

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
variable {jL : Fin Pp} {rowC : IStmt HS Pp} {K r Z Zr H : ℕ}

open _root_.NLogN hiding padL vE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFW hiding RowU RowUP cBody cCL cChain cLowP cLowPart cTot cbW clF coefF
open _root_.IntMul.OpenAI.R129.P.NLogN.KFW

theorem IntMul.OpenAI.R129.P.NLogN.KFW.lvQ_all {Kc : ℝ} (hRow : RowU Isym tbl rowC Kc) (hKc : 0 ≤ Kc)
    (hj : tbl jL = levC jL rowC)
    (hK6 : 6 ≤ K) (hr : 1 ≤ r) (hKZ : 80 * Z * (Z + 2) ≤ 2 ^ K) (hZZ : Z ≤ Zr) (hZr : Zr + 2 ≤ r)
    (hHZ : H + 1 < 2 ^ Z) : ∀ k, LvQ Isym tbl jL rowC K r Z Zr H k (cbW Kc K k) := by sorry
