-- Prove2me | Theorems.Thm_IntMul_OpenAI_R154_P_NLogN_KFM_phi_phase
-- name    : IntMul.OpenAI.R154.P.NLogN.KFM.phi_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T03:16:25.566702+00:00
-- url     : https://prove2.me/theorems/9512b3e9-cc51-472f-9a1c-07102422efb6
-- title:
--   The Φ (forward) and Φ⁻¹ calls. fwd = true calls eF on PhiD, else eB (κ = 2⁻¹⁵⁴ constants)
-- statement:
--   **The Φ (forward) and Φ⁻¹ calls. fwd = true calls eF on PhiD, else eB**, at the `frozen-154` constants.
--
--   This is `NLogN.KFM.phi_phase` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged) with the constants of §8 replaced by those of the community patch `frozen-154`: $\varepsilon = c = 2^{-51}$, $\lambda' = 1 - 2^{-102}$ ($\tau = 1 - 2^{-50}$ and $\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R154`, and every constant-dependent name lives under `IntMul.OpenAI.R154.P`.
--
--   **Context.** The lemma belongs to the part *KFM Big2: the interface calls of `bigE`*: Every interface call is `callW bld X Y dS e` (KFMCall) with the descriptor builder `bld` (KFMSB,
--   KFMSF) on the builder stack `X = bX dS` and the scratch `Y = bY dS` (both differ from the
--   interface's descriptor stack `dS`). A run of the interface in its own table `kTable ext` is a run
--   in the merged table (`IRuns.relabel`).
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the frozen-154 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFM.phi_phase` (https://prove2.me/theorems/d97e389a-303d-4c1c-b6cd-33be7e7ba268).

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
open _root_.AModel hiding hdPos
open _root_.AModelL12
open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR St aE aK cMv cStep cstep gS negP outR pT padL rJ1 rS rT sI stD tB zB zR
open _root_.NLogN.KFB hiding permL permP rB2 rG rN
open _root_.NLogN.KFT hiding carW tE zB
open _root_.NLogN.RS
open _root_.IntMul.HvdH
open _root_.IntMul.OpenAI.RT
open _root_.IntMul.OpenAI.RC
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RCost hiding Ncost c es lam' δ ε κ τ
open _root_.IntMul.OpenAI.R154
variable {P P' : ℕ} {Isym : List Sym} {iprog : Fin P → IStmt HS P}
  {ext : Fin P' → IStmt HS (7 + P')} {g : Fin (7 + P') → Fin P}
  (hprog : ∀ j, iprog (g j) = (kTable ext j).ren id g)
  {n D : ℕ} (hn : n0 ≤ n) (hD : dP n = D + 1)
include hprog hn

open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

theorem IntMul.OpenAI.R154.P.NLogN.KFM.phi_phase {eF eB : Fin (7 + P')} {dS : Fin HS} {C₀ : ℝ} (hd0 : dS ≠ 0)
    (hP : phiG Isym ext eF eB dS C₀ (pP n + 2) (ℓP n - 1) (IntMul.OpenAI.R154.dP n) (bLn n) (srcN n) (muN n))
    (Bd : ℕ) (hBd : ∀ x ∈ descPhiN n, zsz x ≤ Bd)
    (t : IState HS) (hR : BaseOK t n) (xs : List ℤ) (R0 : List Item)
    (h0 : t.G 0 = ints xs ++ R0) (hxw : Bnd (pP n + 2) xs) :
    (xs.length = vol (KFU.shK (IntMul.OpenAI.R154.dP n) (KFU.sP (IntMul.OpenAI.R154.dP n) (srcN n))) →
      ∃ c : ℕ, IRuns Isym iprog (callW (descPhiP (bX dS) rPw) (bX dS) (bY dS) dS (g eF)) t
        (t.upd 0 (ints (KFU.PhiD (ℓP n - 1) (IntMul.OpenAI.R154.dP n) (bLn n) (srcN n) (muN n) xs) ++ R0)) c ∧
        (c : ℝ) ≤ kPhi n Bd C₀) ∧
    (xs.length = vol (KFU.shR (IntMul.OpenAI.R154.dP n) (KFU.tP (IntMul.OpenAI.R154.dP n) (ℓP n - 1) (bLn n))) →
      ∃ c : ℕ, IRuns Isym iprog (callW (descPhiP (bX dS) rPw) (bX dS) (bY dS) dS (g eB)) t
        (t.upd 0 (ints (KFU.PhiInvD (ℓP n - 1) (IntMul.OpenAI.R154.dP n) (bLn n) (srcN n) (muN n) xs) ++ R0)) c ∧
        (c : ℝ) ≤ kPhi n Bd C₀) := by sorry
