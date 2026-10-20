-- Prove2me | Theorems.Thm_IntMul_OpenAI_R154_P_NLogN_KFM_srcS_ok_n
-- name    : IntMul.OpenAI.R154.P.NLogN.KFM.srcS_ok_n
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-20T03:18:44.587003+00:00
-- url     : https://prove2.me/theorems/703d970c-c51b-4ee3-8139-cb70393b698f
-- title:
--   The explicit sources for the parameters of n ≥ n₀ (κ = 2⁻¹⁵⁴ constants)
-- statement:
--   **The explicit sources for the parameters of n ≥ n₀**, at the `frozen-154` constants.
--
--   This is `NLogN.KFM.srcS_ok_n` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged) with the constants of §8 replaced by those of the community patch `frozen-154`: $\varepsilon = c = 2^{-51}$, $\lambda' = 1 - 2^{-102}$ ($\tau = 1 - 2^{-50}$ and $\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R154`, and every constant-dependent name lives under `IntMul.OpenAI.R154.P`.
--
--   **Context.** The lemma belongs to the part *KFM 14: the setup arithmetic (§9.2), in the integer form the machine computes*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the frozen-154 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFM.srcS_ok_n` (https://prove2.me/theorems/84f92dc3-5bb3-4a9e-94e6-bffac6b6c588).

import Definitions.Def_IntMul_OpenAI_R154_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RCost hiding Ncost c es lam' δ ε κ τ
open _root_.IntMul.OpenAI.R154

open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

theorem IntMul.OpenAI.R154.P.NLogN.KFM.srcS_ok_n {n : ℕ} (hn : IntMul.OpenAI.Glue.n0 ≤ n) (d' : ℕ) (hd' : d' ≤ IntMul.OpenAI.R154.dP n) :
    (∀ i : Fin (IntMul.OpenAI.R154.dP n), Odd (srcS (IntMul.OpenAI.R154.dP n) d' (IntMul.OpenAI.R154.rP n) i)) ∧
    (∀ i j : Fin (IntMul.OpenAI.R154.dP n), i ≠ j → Nat.Coprime (srcS (IntMul.OpenAI.R154.dP n) d' (IntMul.OpenAI.R154.rP n) i) (srcS (IntMul.OpenAI.R154.dP n) d' (IntMul.OpenAI.R154.rP n) j)) ∧
    ∀ i : Fin (IntMul.OpenAI.R154.dP n), (4 * IntMul.OpenAI.R154.dP n - 2) * (if (i : ℕ) < d' then IntMul.OpenAI.R154.rP n / 2 else IntMul.OpenAI.R154.rP n) <
        4 * IntMul.OpenAI.R154.dP n * srcS (IntMul.OpenAI.R154.dP n) d' (IntMul.OpenAI.R154.rP n) i ∧
      4 * IntMul.OpenAI.R154.dP n * srcS (IntMul.OpenAI.R154.dP n) d' (IntMul.OpenAI.R154.rP n) i ≤ (4 * IntMul.OpenAI.R154.dP n - 1) * (if (i : ℕ) < d' then IntMul.OpenAI.R154.rP n / 2 else IntMul.OpenAI.R154.rP n) := by sorry
