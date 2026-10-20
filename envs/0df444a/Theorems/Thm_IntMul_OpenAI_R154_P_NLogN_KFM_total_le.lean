-- Prove2me | Theorems.Thm_IntMul_OpenAI_R154_P_NLogN_KFM_total_le
-- name    : IntMul.OpenAI.R154.P.NLogN.KFM.total_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-20T03:19:01.49964+00:00
-- url     : https://prove2.me/theorems/788b3a13-b770-428d-bcc7-e00834bf9336
-- title:
--   total_le (KFM Final: `PhiNeed ∧ LineNeed ∧ ChirpNeedR → KappaBound (1/2^182)`) (κ = 2⁻¹⁵⁴ constants)
-- statement:
--   **total_le (KFM Final: `PhiNeed ∧ LineNeed ∧ ChirpNeedR → R154.P.MachineGoal`)**, at the `frozen-154` constants.
--
--   This is `NLogN.KFM.total_le` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged) with the constants of §8 replaced by those of the community patch `frozen-154`: $\varepsilon = c = 2^{-51}$, $\lambda' = 1 - 2^{-102}$ ($\tau = 1 - 2^{-50}$ and $\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R154`, and every constant-dependent name lives under `IntMul.OpenAI.R154.P`.
--
--   **Context.** The lemma belongs to the part *KFM Final: `PhiNeed ∧ LineNeed ∧ ChirpNeedR → R154.P.MachineGoal`*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the frozen-154 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFM.total_le` (https://prove2.me/theorems/18604bae-858b-4410-ae1d-5f1dcf20fb4d).

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
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

theorem IntMul.OpenAI.R154.P.NLogN.KFM.total_le {n D : ℕ} (hn : IntMul.OpenAI.Glue.n0 ≤ n) (hD : IntMul.OpenAI.R154.dP n = D + 1) {CΦ CL CC : ℝ} (h1 : 0 ≤ CΦ)
    (h2 : 0 ≤ CL) (h3 : 0 ≤ CC) (AL AC : ℕ) (x y : List Bool) (hx : x.length = n) :
    (IntMul.OpenAI.R154.P.NLogN.KFM.setC x y : ℝ) + kBigF n D (dzB (descPhiN n)) (dzB (descLineN n)) (dzB (descChirpN n)) AL AC
      CΦ CL CC + 2 ≤ Ctot CΦ CL CC * cLineU n (AL + AC + 2) := by sorry
