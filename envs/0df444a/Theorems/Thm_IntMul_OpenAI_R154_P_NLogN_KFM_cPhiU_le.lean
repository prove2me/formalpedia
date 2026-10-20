-- Prove2me | Theorems.Thm_IntMul_OpenAI_R154_P_NLogN_KFM_cPhiU_le
-- name    : IntMul.OpenAI.R154.P.NLogN.KFM.cPhiU_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-20T03:17:02.834386+00:00
-- url     : https://prove2.me/theorems/dfec02c6-658e-44d8-b76a-1347edb04dd4
-- title:
--   cPhiU_le (KFM Cost: the cost of `bigE` in the unit `ZU`) (κ = 2⁻¹⁵⁴ constants)
-- statement:
--   **cPhiU_le (KFM Cost: the cost of `bigE` in the unit `ZU`)**, at the `frozen-154` constants.
--
--   This is `NLogN.KFM.cPhiU_le` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged) with the constants of §8 replaced by those of the community patch `frozen-154`: $\varepsilon = c = 2^{-51}$, $\lambda' = 1 - 2^{-102}$ ($\tau = 1 - 2^{-50}$ and $\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R154`, and every constant-dependent name lives under `IntMul.OpenAI.R154.P`.
--
--   **Context.** The lemma belongs to the part *KFM Cost: the cost of `bigE` in the unit `ZU`*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the frozen-154 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFM.cPhiU_le` (https://prove2.me/theorems/f520a4a3-b2e7-4144-8e65-c73e4b72f783).

import Definitions.Def_IntMul_OpenAI_R154_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM
open Finset
open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR St aE aK cMv cStep cstep gS negP outR pT padL rJ1 rS rT sI stD tB zB zR
open _root_.NLogN.KFB hiding permL permP rB2 rG rN
open _root_.NLogN.KFT hiding carW tE zB
open _root_.NLogN.KFU hiding cMv oA oC oD zD
open _root_.NLogN.RS
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RCost hiding Ncost c es lam' δ ε κ τ
open _root_.IntMul.OpenAI.R154
set_option maxHeartbeats 2000000

open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

theorem IntMul.OpenAI.R154.P.NLogN.KFM.cPhiU_le {n D : ℕ} (hn : IntMul.OpenAI.Glue.n0 ≤ n) (hD : IntMul.OpenAI.R154.dP n = D + 1) :
    cPhiU (pP n + 2) (ℓP n - 1) (IntMul.OpenAI.R154.dP n) (bLn n) (srcN n) ≤
      10 ^ 9 * ((IntMul.OpenAI.Glue.TP n : ℝ) * pP n * NcN n) + 10 ^ 4 * ((bP n + 1) ^ 6 : ℕ) := by sorry
