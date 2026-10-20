-- Prove2me | Theorems.Thm_IntMul_OpenAI_R154_P_NLogN_KFV_p18IL_at
-- name    : IntMul.OpenAI.R154.P.NLogN.KFV.p18IL_at
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-20T03:18:58.276312+00:00
-- url     : https://prove2.me/theorems/5b1e18d9-959d-4b9f-acc7-fc6bbd51c444
-- title:
--   The uniform Proposition 18, from the uniform Proposition 14 at A and the width condition at A (κ = 2⁻¹⁵⁴ constants)
-- statement:
--   **The uniform Proposition 18, from the uniform Proposition 14 at A and the width condition at A**, at the `frozen-154` constants.
--
--   This is `NLogN.KFV.p18IL_at` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged) with the constants of §8 replaced by those of the community patch `frozen-154`: $\varepsilon = c = 2^{-51}$, $\lambda' = 1 - 2^{-102}$ ($\tau = 1 - 2^{-50}$ and $\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R154`, and every constant-dependent name lives under `IntMul.OpenAI.R154.P`.
--
--   **Context.** The lemma belongs to the part *KFV §62: the uniform Proposition 18 at a gate-class constant `A`*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the frozen-154 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFV.p18IL_at` (https://prove2.me/theorems/b50a499e-6186-4679-9ca0-0c55c901484c).

import Definitions.Def_IntMul_OpenAI_R154_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open _root_.NLogN hiding posE tE twA twB vE zX
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFV hiding Cost18 EwB18 Log18Need P14Need P14Uat Par18Need cChunk total18
open _root_.IntMul.OpenAI.R154.P.NLogN.KFV

open _root_.NLogN hiding posE tE twA twB vE zX
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFV hiding Cost18 EwB18 Log18Need P14Need P14Uat Par18Need cChunk total18
open _root_.IntMul.OpenAI.R154.P.NLogN.KFV

theorem IntMul.OpenAI.R154.P.NLogN.KFV.p18IL_at (A : ℕ) (HU : P14Uat A) (HE : EwB18 A) : IntMul.OpenAI.R154.P.NLogN.KFM.P18IL := by sorry
