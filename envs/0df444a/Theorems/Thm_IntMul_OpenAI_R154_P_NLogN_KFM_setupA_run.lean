-- Prove2me | Theorems.Thm_IntMul_OpenAI_R154_P_NLogN_KFM_setupA_run
-- name    : IntMul.OpenAI.R154.P.NLogN.KFM.setupA_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T03:16:47.782786+00:00
-- url     : https://prove2.me/theorems/0452d69f-0e93-47e7-ba9e-1759cea7f141
-- title:
--   setupA_run (KFM S3: the scalar setup parameters as counts (math side)) (κ = 2⁻¹⁵⁴ constants)
-- statement:
--   **setupA_run (KFM S3: the scalar setup parameters as counts (math side))**, at the `frozen-154` constants.
--
--   This is `NLogN.KFM.setupA_run` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged) with the constants of §8 replaced by those of the community patch `frozen-154`: $\varepsilon = c = 2^{-51}$, $\lambda' = 1 - 2^{-102}$ ($\tau = 1 - 2^{-50}$ and $\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R154`, and every constant-dependent name lives under `IntMul.OpenAI.R154.P`.
--
--   **Context.** The lemma belongs to the part *KFM S3: the scalar setup parameters as counts (math side)*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the frozen-154 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFM.setupA_run` (https://prove2.me/theorems/f7c425dd-3451-49fe-a750-9a1a24a40f43).

import Definitions.Def_IntMul_OpenAI_R154_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.IntMul
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.NLogN.RS
set_option maxHeartbeats 2000000

open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

theorem IntMul.OpenAI.R154.P.NLogN.KFM.setupA_run (n : ℕ) (hn : n0 ≤ n) (s : IState HS) (LB : List Item)
    (hB : s.G zB = .int (bP n : ℤ) :: LB) :
    setupA.ok s ∧ setupA.run s = ((s.upd NLogN.KFM.zD (.int (dP n : ℤ) :: s.G NLogN.KFM.zD)).upd zK
      (.int (KP n : ℤ) :: s.G zK)).upd zAl (.int (αP n : ℤ) :: s.G zAl) := by sorry
