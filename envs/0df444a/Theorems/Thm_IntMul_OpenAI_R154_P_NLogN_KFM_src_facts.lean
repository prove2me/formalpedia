-- Prove2me | Theorems.Thm_IntMul_OpenAI_R154_P_NLogN_KFM_src_facts
-- name    : IntMul.OpenAI.R154.P.NLogN.KFM.src_facts
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-20T03:18:44.876189+00:00
-- url     : https://prove2.me/theorems/96b0750d-1a1e-4ba8-9279-b0dc15c5f3a0
-- title:
--   src_facts (KFM S8: the source and inverse lists for the parameters of `n`) (κ = 2⁻¹⁵⁴ constants)
-- statement:
--   **src_facts (KFM S8: the source and inverse lists for the parameters of `n`)**, at the `frozen-154` constants.
--
--   This is `NLogN.KFM.src_facts` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged) with the constants of §8 replaced by those of the community patch `frozen-154`: $\varepsilon = c = 2^{-51}$, $\lambda' = 1 - 2^{-102}$ ($\tau = 1 - 2^{-50}$ and $\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R154`, and every constant-dependent name lives under `IntMul.OpenAI.R154.P`.
--
--   **Context.** The lemma belongs to the part *KFM S8: the source and inverse lists for the parameters of `n`*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the frozen-154 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFM.src_facts` (https://prove2.me/theorems/d18a1cdf-a7c4-40f0-b9c2-a5d603f7f7a7).

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
open _root_.IntMul.OpenAI.RP
open _root_.NLogN.RS

open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

theorem IntMul.OpenAI.R154.P.NLogN.KFM.src_facts {n : ℕ} (hn : IntMul.OpenAI.Glue.n0 ≤ n) (j : ℕ) (hj : j < IntMul.OpenAI.R154.dP n) :
    (j < dpN n → j ≤ srcM (IntMul.OpenAI.R154.dP n) (IntMul.OpenAI.R154.rP n) (IntMul.OpenAI.R154.rP n / 2)) ∧
    (dpN n ≤ j → j - dpN n ≤ srcM (IntMul.OpenAI.R154.dP n) (IntMul.OpenAI.R154.rP n) (IntMul.OpenAI.R154.rP n)) ∧
    2 ≤ srcN n j ∧ srcN n j ≤ IntMul.OpenAI.R154.rP n ∧ Nat.Coprime (prodN n j) (srcN n j) := by sorry
