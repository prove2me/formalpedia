-- Prove2me | Theorems.Thm_IntMul_OpenAI_R154_P_NLogN_KFM_lineB_phase
-- name    : IntMul.OpenAI.R154.P.NLogN.KFM.lineB_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T03:16:13.834484+00:00
-- url     : https://prove2.me/theorems/20fea35c-d5a4-444f-9f3e-00f55b6cde2b
-- title:
--   The B₀-lines call (κ = 2⁻¹⁵⁴ constants)
-- statement:
--   **The B₀-lines call**, at the `frozen-154` constants.
--
--   This is `NLogN.KFM.lineB_phase` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged) with the constants of §8 replaced by those of the community patch `frozen-154`: $\varepsilon = c = 2^{-51}$, $\lambda' = 1 - 2^{-102}$ ($\tau = 1 - 2^{-50}$ and $\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R154`, and every constant-dependent name lives under `IntMul.OpenAI.R154.P`.
--
--   **Context.** The lemma belongs to the part *KFM Big2: the interface calls of `bigE`*: Every interface call is `callW bld X Y dS e` (KFMCall) with the descriptor builder `bld` (KFMSB,
--   KFMSF) on the builder stack `X = bX dS` and the scratch `Y = bY dS` (both differ from the
--   interface's descriptor stack `dS`). A run of the interface in its own table `kTable ext` is a run
--   in the merged table (`IRuns.relabel`).
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the frozen-154 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFM.lineB_phase` (https://prove2.me/theorems/116ce223-c8a2-40f6-a161-79331757e16e).

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

theorem IntMul.OpenAI.R154.P.NLogN.KFM.lineB_phase [instS : ∀ i, NeZero (sBD n D i)] [instT : ∀ i, NeZero (tBD n D i)]
    {eA eB : Fin (7 + P')} {dS : Fin HS} {C₀ : ℝ} {A : ℕ} (hd0 : dS ≠ 0)
    (hL : lineG Isym ext eA eB dS C₀ A n (D + 1)) (Bd : ℕ) (hBd : ∀ x ∈ descLineN n, zsz x ≤ Bd)
    (t : IState HS) (hR : BaseOK t n) (ys : List GI) (y : ((i : Fin (D + 1)) → ZMod (tBD n D i)) → ℂ)
    (R0 : List Item) (h0 : t.G 0 = ints (gflat ys) ++ R0)
    (hy : RepFull (pP n) (tBD n D) ys y) (hy1 : ‖y‖ ≤ 1) :
    ∃ (ys' : List GI) (v : ((i : Fin (D + 1)) → ZMod (sBD n D i)) → ℂ) (c : ℕ),
      IRuns Isym iprog (callW (descLineP (bX dS)) (bX dS) (bY dS) dS (g eB)) t
        (t.upd 0 (ints (gflat ys') ++ R0)) c ∧
      RepPad (pP n) (sBD n D) (tBD n D) ys' v ∧ NLogN.KFB.GB (pP n + 2) ys' ∧
      (∀ M : AxisMaps (d := D + 1) (pP n) (αP n) (sBD n D) (tBD n D),
        ‖v - tensCLM (kerB M.B) y‖ ≤ epsB (pP n) (αP n) (sBD n D) (tBD n D) * hp (pP n)) ∧
      (c : ℝ) ≤ kLine n Bd C₀ A := by sorry
