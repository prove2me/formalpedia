-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFM_desc_chirp
-- name    : IntMul.OpenAI.R129.P.NLogN.KFM.desc_chirp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:26:36.817428+00:00
-- url     : https://prove2.me/theorems/5b006761-bac9-452c-8886-995cb6e93202
-- title:
--   desc_chirp (KFM Cost: the cost of `bigE` in the unit `ZU`) (κ = 2⁻¹²⁹ constants)
-- statement:
--   **desc_chirp (KFM Cost: the cost of `bigE` in the unit `ZU`)**, at the `same-network-129` constants.
--
--   This is `NLogN.KFM.desc_chirp` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFM Cost: the cost of `bigE` in the unit `ZU`*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFM.desc_chirp` (https://prove2.me/theorems/25042c1d-d400-4932-b131-2f5e05f3a347).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL PhiNeed QRegs SwapNeed TrRegs TransNeed bLn baseSt bigP bsN cLineU cPhiU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV phiG prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM
open Finset
open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR St aE aK cMv cStep cstep gS negP outR pT padL rJ1 rS rT sI stD tB zB zR
open _root_.NLogN.KFB hiding permL permP rB2 rG rN
open _root_.NLogN.KFT hiding carW tE zB
open _root_.NLogN.KFU hiding SwOK cMv cPhi oA oC oD zD
open _root_.IntMul.OpenAI.R129.P.NLogN.KFU
open _root_.NLogN.RS
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R129
open _root_.IntMul.OpenAI.RCost hiding Ncost c es lam' δ ε κ τ
open _root_.IntMul.OpenAI.R129
variable {n : ℕ} (hn : n0 ≤ n)
include hn

open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL PhiNeed QRegs SwapNeed TrRegs TransNeed bLn baseSt bigP bsN cLineU cPhiU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV phiG prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM

theorem IntMul.OpenAI.R129.P.NLogN.KFM.desc_chirp : ∀ x ∈ descChirpN n, 0 ≤ x ∧ x ≤ 2 ^ bP n := by sorry
