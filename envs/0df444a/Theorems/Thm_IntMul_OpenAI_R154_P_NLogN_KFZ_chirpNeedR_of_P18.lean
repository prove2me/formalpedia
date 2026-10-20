-- Prove2me | Theorems.Thm_IntMul_OpenAI_R154_P_NLogN_KFZ_chirpNeedR_of_P18
-- name    : IntMul.OpenAI.R154.P.NLogN.KFZ.chirpNeedR_of_P18
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-20T03:21:51.444894+00:00
-- url     : https://prove2.me/theorems/58b69b7c-ba97-4cea-a2cd-50eb46a5a957
-- title:
--   chirpNeedR_of_P18 (KFZ Main: `P18IL → ChirpNeedR`) (κ = 2⁻¹⁵⁴ constants)
-- statement:
--   **chirpNeedR_of_P18 (KFZ Main: `P18IL → ChirpNeedR`)**, at the `frozen-154` constants.
--
--   This is `NLogN.KFZ.chirpNeedR_of_P18` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged) with the constants of §8 replaced by those of the community patch `frozen-154`: $\varepsilon = c = 2^{-51}$, $\lambda' = 1 - 2^{-102}$ ($\tau = 1 - 2^{-50}$ and $\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R154`, and every constant-dependent name lives under `IntMul.OpenAI.R154.P`.
--
--   **Context.** The lemma belongs to the part *KFZ Main: `P18IL → ChirpNeedR`*: The chirp procedure `body` (`KFZFull`) is kmain's own procedure `0` in the merged table
--   `mExt ext₁₈ ∅ ∅ [body]`; the Prop 18 procedure is reached through `gI` (`mTable_g1`,
--   `IRuns.relabel`). The descriptor stack is `cS = 36` (the chirp descriptor stays there and is
--   restored by `setupP`).
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the frozen-154 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFZ.chirpNeedR_of_P18` (https://prove2.me/theorems/55c562f8-9e3c-4faa-be0c-da2f6e6b8dde).

import Definitions.Def_IntMul_OpenAI_R154_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open _root_.NLogN hiding St T1 T2 T3 T4 T5 T6 T7 tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFZ hiding BN ChirpNeedR bitN bsN hN length_bsN length_ssN ssN σN
open _root_.IntMul.OpenAI.R154.P.NLogN.KFZ
open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR St aE cBody negP outR padL pushF pushes
open _root_.NLogN.KFB hiding permL permP qA qT
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DE DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bitE bsN cLineU chirpGN descChirpN descLineN descPhiN dpN eB eN fmB gapR gconj kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm liftL lineG muN parC parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD sumB tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RCost hiding Ncost c es lam' δ ε κ τ
open _root_.IntMul.OpenAI.R154

open _root_.NLogN hiding St T1 T2 T3 T4 T5 T6 T7 tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFZ hiding BN ChirpNeedR bitN bsN hN length_bsN length_ssN ssN σN
open _root_.IntMul.OpenAI.R154.P.NLogN.KFZ

theorem IntMul.OpenAI.R154.P.NLogN.KFZ.chirpNeedR_of_P18 (H : P18IL) : ChirpNeedR := by sorry
