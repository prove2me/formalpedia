-- Prove2me | Theorems.Thm_IntMul_OpenAI_R154_P_NLogN_KFV_cost18_of
-- name    : IntMul.OpenAI.R154.P.NLogN.KFV.cost18_of
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-20T03:18:53.06315+00:00
-- url     : https://prove2.me/theorems/21cd3dde-1f2d-481a-a275-1adff29a8e9a
-- title:
--   The asymptotic cost of a Proposition 18 call, from the numeric side conditions and the logarithmic factor… (κ = 2⁻¹⁵⁴ constants)
-- statement:
--   **The asymptotic cost of a Proposition 18 call, from the numeric side conditions and the logarithmic factor…**, at the `frozen-154` constants.
--
--   This is `NLogN.KFV.cost18_of` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged) with the constants of §8 replaced by those of the community patch `frozen-154`: $\varepsilon = c = 2^{-51}$, $\lambda' = 1 - 2^{-102}$ ($\tau = 1 - 2^{-50}$ and $\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R154`, and every constant-dependent name lives under `IntMul.OpenAI.R154.P`.
--
--   **Context.** The lemma belongs to the part *KFV §61: the asymptotic cost of a Proposition 18 call (`Cost18`)*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the frozen-154 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFV.cost18_of` (https://prove2.me/theorems/783ff275-5ca5-4a5c-bf03-6628c6038c45).

import Definitions.Def_IntMul_OpenAI_R154_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open _root_.NLogN hiding posE tE twA twB vE zX
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFV hiding Cost18 EwB18 Log18Need P14Need P14Uat Par18Need cChunk total18
open _root_.IntMul.OpenAI.R154.P.NLogN.KFV
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
open _root_.GlueLayout
open _root_.GlueP14 hiding blk cRec
open _root_.GlueError
open _root_.IntMul.OpenAI.Glue hiding KP LP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RCost hiding Ncost c es lam' δ ε κ τ
open _root_.IntMul.OpenAI.R154
set_option maxHeartbeats 8000000

open _root_.NLogN hiding posE tE twA twB vE zX
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFV hiding Cost18 EwB18 Log18Need P14Need P14Uat Par18Need cChunk total18
open _root_.IntMul.OpenAI.R154.P.NLogN.KFV

theorem IntMul.OpenAI.R154.P.NLogN.KFV.cost18_of (HPar : Par18Need) (HL : Log18Need) : Cost18 := by sorry
