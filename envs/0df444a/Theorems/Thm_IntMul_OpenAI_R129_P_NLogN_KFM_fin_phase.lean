-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFM_fin_phase
-- name    : IntMul.OpenAI.R129.P.NLogN.KFM.fin_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:26:41.754697+00:00
-- url     : https://prove2.me/theorems/3069485b-33a3-4da2-b195-a7e9812e4ced
-- title:
--   The read-out (κ = 2⁻¹²⁹ constants)
-- statement:
--   **The read-out**, at the `same-network-129` constants.
--
--   This is `NLogN.KFM.fin_phase` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFM Big9: the read-out*: After the rounding passes (`finA`), `Φ⁻¹; carries; write` outputs `bin(2n, x·y)`.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFM.fin_phase` (https://prove2.me/theorems/3c5e9808-f3a3-4f4f-bdd2-94e3167fd76d).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 20000
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL PhiNeed QRegs SwapNeed TrRegs TransNeed bLn baseSt bigP bsN cLineU cPhiU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV phiG prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM
open Finset
open _root_.AModel hiding hdPos
open _root_.AModelL12
open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR St aE aK cMv cStep cstep gS negP outR pT padL rJ1 rS rT sI stD tB zB zR
open _root_.NLogN.KFB hiding permL permP rB2 rG rN
open _root_.NLogN.KFT hiding carW tE zB
open _root_.NLogN.KFU hiding SwOK cMv cPhi oA oC oD zD
open _root_.IntMul.OpenAI.R129.P.NLogN.KFU
open _root_.NLogN.RS
open _root_.IntMul.HvdH
open _root_.IntMul.OpenAI.RT
open _root_.IntMul.OpenAI.RC
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R129
open _root_.IntMul.OpenAI.RCost hiding Ncost c es lam' δ ε κ τ
open _root_.IntMul.OpenAI.R129
variable {E : ℕ} {ix : Ix (7 + E)} {Isym : List Sym} {extM : Fin E → IStmt HS (7 + E)} {n D : ℕ}
  [instS : ∀ i, NeZero (sBD n D i)] [instT : ∀ i, NeZero (tBD n D i)]
set_option maxHeartbeats 8000000

open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL PhiNeed QRegs SwapNeed TrRegs TransNeed bLn baseSt bigP bsN cLineU cPhiU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV phiG prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM

theorem IntMul.OpenAI.R129.P.NLogN.KFM.fin_phase (C : BigCtx ix Isym extM n D) (t : IState HS) (hR : BaseOK t n) (x y : ℕ)
    (hx : x < 2 ^ n) (hy : y < 2 ^ n) (zsZ : List GI)
    (Z : ((i : Fin (D + 1)) → ZMod (sBD n D i)) → ℂ)
    (h0 : t.G 0 = ints (gflat zsZ)) (hZ : RepPad (pP n) (sBD n D) (tBD n D) zsZ Z)
    (hg : NLogN.KFB.GB (IntMul.OpenAI.R129.P.NLogN.KFM.wU n D) zsZ) (hcl : Close C x y Z) (hout : t.out = []) :
    ∃ s' c, IRuns Isym (kTable extM) (finP ix) t s' c ∧ s'.out = bin (2 * n) (x * y) ∧
      (c : ℝ) ≤ kFin C := by sorry
