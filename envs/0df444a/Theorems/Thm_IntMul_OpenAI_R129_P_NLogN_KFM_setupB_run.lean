-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFM_setupB_run
-- name    : IntMul.OpenAI.R129.P.NLogN.KFM.setupB_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:06.627502+00:00
-- url     : https://prove2.me/theorems/00c40cd2-2400-44b6-9002-f32db136cb28
-- title:
--   setupB_run (KFM S3: the scalar setup parameters as counts (math side)) (κ = 2⁻¹²⁹ constants)
-- statement:
--   **setupB_run (KFM S3: the scalar setup parameters as counts (math side))**, at the `same-network-129` constants.
--
--   This is `NLogN.KFM.setupB_run` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFM S3: the scalar setup parameters as counts (math side)*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFM.setupB_run` (https://prove2.me/theorems/bbb9055b-f1f4-45ab-b320-d4ff6887e4db).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL PhiNeed QRegs SwapNeed TrRegs TransNeed bLn baseSt bigP bsN cLineU cPhiU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV phiG prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM
open _root_.IntMul
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R129
open _root_.NLogN.RS
open _root_.IntMul.OpenAI.RP
set_option maxHeartbeats 2000000

open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL PhiNeed QRegs SwapNeed TrRegs TransNeed bLn baseSt bigP bsN cLineU cPhiU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV phiG prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM

theorem IntMul.OpenAI.R129.P.NLogN.KFM.setupB_run (n : ℕ) (hn : n0 ≤ n) (s : IState HS) (LN LB LD : List Item)
    (hN : s.G zN = .int (n : ℤ) :: LN) (hB : s.G zB = .int (bP n : ℤ) :: LB)
    (hD : s.G NLogN.KFM.zD = .int (dP n : ℤ) :: LD) :
    setupB.ok s ∧ setupB.run s = (((s.upd zL (.int (LP n : ℤ) :: s.G zL)).upd zEl
      (.int (ℓP n : ℤ) :: s.G zEl)).upd zR (.int (IntMul.OpenAI.R129.rP n : ℤ) :: s.G zR)).upd zDp
      (.int (mcnt (LP n) (dP n) : ℤ) :: s.G zDp) := by sorry
