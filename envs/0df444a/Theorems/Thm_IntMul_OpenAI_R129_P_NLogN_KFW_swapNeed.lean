-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFW_swapNeed
-- name    : IntMul.OpenAI.R129.P.NLogN.KFW.swapNeed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:34.764741+00:00
-- url     : https://prove2.me/theorems/277b8f6a-eea8-474f-a23d-6ded59c70fbb
-- title:
--   SwapNeed: uniform Lemma 12 on Gaussian arrays, in the merged table kTable with one extra procedure (swGU… (κ = 2⁻¹²⁹ constants)
-- statement:
--   **SwapNeed: uniform Lemma 12 on Gaussian arrays, in the merged table kTable with one extra procedure (swGU…**, at the `same-network-129` constants.
--
--   This is `NLogN.KFW.swapNeed` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFW: uniform Lemma 12 on Gaussian arrays (`SwapNeed`)*: `swGU q = descP ; swWU q ; popP`: read the descriptor `descSw w u p q sh` on `dS` into the
--   registers of `swWU` (`descP`), run the register-driven integer swap on the shape `sh ++ [2]`,
--   and pop the registers again.  **`swGU_spec`**, and **`swapNeed : KFM.SwapNeed`** with the table
--   `kTable (fun _ => (swGU q).ren id (gL 1))` (one fixed prime `q`).
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFW.swapNeed` (https://prove2.me/theorems/4f09fc94-4bf1-4eae-afae-f506e36b5bc1).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open _root_.NLogN hiding padL vE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFW hiding RowU RowUP cBody cCL cChain cLowP cLowPart cTot cbW clF coefF
open _root_.IntMul.OpenAI.R129.P.NLogN.KFW
open _root_.IntMul
open _root_.NLogN.RS
open _root_.NLogN.KFW.RS
open _root_.NLogN.KIL hiding Cfg FR FrOK St aE bodyU cBody fIn kS negP outR pT padL rowR stD
open _root_.NLogN.KFD hiding levF scr
open _root_.NLogN.KFB hiding permL permP
open _root_.NLogN.KFS hiding τS
open _root_.IntMul.OpenAI.R129.P.NLogN.KFS
open _root_.NLogN.KFL hiding LinesOK P1 SwOK cT coreCost sT uE
open _root_.IntMul.OpenAI.R129.P.NLogN.KFL
open _root_.AModel hiding hdPos logStep stepC
open _root_.AModelL12

open _root_.NLogN hiding padL vE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFW hiding RowU RowUP cBody cCL cChain cLowP cLowPart cTot cbW clF coefF
open _root_.IntMul.OpenAI.R129.P.NLogN.KFW

theorem IntMul.OpenAI.R129.P.NLogN.KFW.swapNeed : IntMul.OpenAI.R129.P.NLogN.KFM.SwapNeed := by sorry
