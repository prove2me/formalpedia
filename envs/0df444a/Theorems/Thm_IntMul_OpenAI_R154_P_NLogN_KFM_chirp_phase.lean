-- Prove2me | Theorems.Thm_IntMul_OpenAI_R154_P_NLogN_KFM_chirp_phase
-- name    : IntMul.OpenAI.R154.P.NLogN.KFM.chirp_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T03:16:22.2459+00:00
-- url     : https://prove2.me/theorems/b960410d-8bf5-453b-bb7d-2097660af0d9
-- title:
--   The chirp call (κ = 2⁻¹⁵⁴ constants)
-- statement:
--   **The chirp call**, at the `frozen-154` constants.
--
--   This is `NLogN.KFM.chirp_phase` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged) with the constants of §8 replaced by those of the community patch `frozen-154`: $\varepsilon = c = 2^{-51}$, $\lambda' = 1 - 2^{-102}$ ($\tau = 1 - 2^{-50}$ and $\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R154`, and every constant-dependent name lives under `IntMul.OpenAI.R154.P`.
--
--   **Context.** The lemma belongs to the part *KFM Big2: the interface calls of `bigE`*: Every interface call is `callW bld X Y dS e` (KFMCall) with the descriptor builder `bld` (KFMSB,
--   KFMSF) on the builder stack `X = bX dS` and the scratch `Y = bY dS` (both differ from the
--   interface's descriptor stack `dS`). A run of the interface in its own table `kTable ext` is a run
--   in the merged table (`IRuns.relabel`).
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the frozen-154 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFM.chirp_phase` (https://prove2.me/theorems/28380cdb-6b95-4678-b40d-82e3be378805).

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

theorem IntMul.OpenAI.R154.P.NLogN.KFM.chirp_phase [∀ i, NeZero (tBD n D i)] {eC : Fin (7 + P')} {dS : Fin HS} {C₀ : ℝ} {A : ℕ}
    {θt θit at' bt : ((i : Fin (D + 1)) → ZMod (tBD n D i)) → ℂ} (hd0 : dS ≠ 0)
    (hC : chirpGN Isym ext eC dS C₀ A n D θt θit at' bt) (Bd : ℕ)
    (hBd : ∀ x ∈ descChirpN n, zsz x ≤ Bd)
    (t : IState HS) (hR : BaseOK t n) (xs : List GI) (x : ((i : Fin (D + 1)) → ZMod (tBD n D i)) → ℂ)
    (R0 : List Item) (h0 : t.G 0 = ints (gflat xs) ++ R0)
    (hx : RepFull (pP n) (tBD n D) xs x) (hx1 : ‖x‖ ≤ 6 / 10) :
    ∃ (Mrt : (((i : Fin (D + 1)) → ZMod (tBD n D i)) → ℂ) →
          (((i : Fin (D + 1)) → ZMod (tBD n D i)) → ℂ) →
          (((i : Fin (D + 1)) → ZMod (tBD n D i)) → ℂ)),
      (∀ f g, Grid (pP n) f → Grid (pP n) g → ‖f‖ ≤ 1 → ‖g‖ ≤ 1 →
        ‖Mrt f g - mrX (tBD n D) f g‖ ≤ ErC n D * hp (pP n)) ∧
    ∃ (ys : List GI) (c : ℕ),
      IRuns Isym iprog (callW (descChirpP (bX dS)) (bX dS) (bY dS) dS (g eC)) t
        (t.upd 0 (ints (gflat ys) ++ R0)) c ∧
      RepFull (pP n) (tBD n D) ys (chirpT (pP n) (mcT (pP n) Mrt θt θit) bt at' x) ∧
      NLogN.KFB.GB (pP n + 2) ys ∧ (c : ℝ) ≤ kChirp n Bd C₀ A := by sorry
