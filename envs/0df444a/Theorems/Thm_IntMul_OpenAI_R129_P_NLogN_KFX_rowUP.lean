-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFX_rowUP
-- name    : IntMul.OpenAI.R129.P.NLogN.KFX.rowUP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:25.958226+00:00
-- url     : https://prove2.me/theorems/fc27556c-0156-4272-a258-95ad802a5839
-- title:
--   RowUP: the uniform Lemma 13 row addition, as the code (rowCodeU q).ren id (gL E) in every extension… (κ = 2⁻¹²⁹ constants)
-- statement:
--   **RowUP: the uniform Lemma 13 row addition, as the code (rowCodeU q).ren id (gL E) in every extension…**, at the `same-network-129` constants.
--
--   This is `NLogN.KFX.rowUP` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFX §7: `RowUP`, the uniform Lemma 13 row addition*: `rowCodeU q` (over `l12prog`) implements `Pm i j` in `SImplQ` form for every admissible parameter
--   set read from the background registers `36 … 45` (`rowQ`).  The Lemma 13 cost `⌈bnd⌉` plus the
--   header cost `cHd` is absorbed into `bnd` with the constant `Kc + 8·10^12`, and `ceil_bnd_le` turns
--   it into the `RowU` form.  The code is placed in `KFM.kTable ext` by relabelling the `l12prog`
--   calls (`kTable_l12`); no extra procedures are needed (`nR = 0`).
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFX.rowUP` (https://prove2.me/theorems/45df6a3d-ba6b-4cb6-a50c-75d8fe15477f).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 20000
open _root_.NLogN
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFX hiding L13U SwEOK
open _root_.IntMul.OpenAI.R129.P.NLogN.KFX
open _root_.IntMul
open _root_.NLogN.RS
open _root_.NLogN.KIL hiding Cfg FR St aE negP outR padL zB
open _root_.NLogN.KFD
open _root_.NLogN.KFE
open _root_.NLogN.KFB hiding cZ permL permP
open _root_.NLogN.KFL hiding LinesOK P1 SwOK cZ coreCost rX
open _root_.IntMul.OpenAI.R129.P.NLogN.KFL
open _root_.NLogN.KFW hiding RowU RowUP cBody cCL cChain cLowP cLowPart cTot cbW clF coefF eBp padL vE
open _root_.IntMul.OpenAI.R129.P.NLogN.KFW
open _root_.NLogN.KFH
open _root_.AModel hiding hdPos
open _root_.Butterfly hiding Op
open _root_.NLogN.KFN hiding pcs τ50
open _root_.IntMul.OpenAI.R129.P.NLogN.KFN
open _root_.P8Lift

open _root_.NLogN
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFX hiding L13U SwEOK
open _root_.IntMul.OpenAI.R129.P.NLogN.KFX

theorem IntMul.OpenAI.R129.P.NLogN.KFX.rowUP : IntMul.OpenAI.R129.P.NLogN.KFW.RowUP := by sorry
