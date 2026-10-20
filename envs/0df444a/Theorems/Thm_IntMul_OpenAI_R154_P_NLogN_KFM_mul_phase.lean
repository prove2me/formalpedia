-- Prove2me | Theorems.Thm_IntMul_OpenAI_R154_P_NLogN_KFM_mul_phase
-- name    : IntMul.OpenAI.R154.P.NLogN.KFM.mul_phase
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-20T03:17:23.955618+00:00
-- url     : https://prove2.me/theorems/00e77865-a992-4d22-bb6e-32db9c0a4ac8
-- title:
--   The product (κ = 2⁻¹⁵⁴ constants)
-- statement:
--   **The product**, at the `frozen-154` constants.
--
--   This is `NLogN.KFM.mul_phase` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged) with the constants of §8 replaced by those of the community patch `frozen-154`: $\varepsilon = c = 2^{-51}$, $\lambda' = 1 - 2^{-102}$ ($\tau = 1 - 2^{-50}$ and $\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R154`, and every constant-dependent name lives under `IntMul.OpenAI.R154.P`.
--
--   **Context.** The lemma belongs to the part *KFM Big7: the product `Z`*: `mulP = inP; mv² 0 → pW; inP; gmul; conj; F̃`. From `ARGM = [y, x]` it leaves on stack `0` an array
--   `Z` with `‖Z − R F_s(cnj Q_p(U_x U_y))‖ ≤ Es hp`, where `U_x, U_y` are the transforms of the two
--   inputs (`inP_phase`).
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the frozen-154 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFM.mul_phase` (https://prove2.me/theorems/a5155544-6469-40fc-9e10-792be4bb64ee).

import Definitions.Def_IntMul_OpenAI_R154_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 20000
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
open _root_.NLogN.KFU hiding cMv oA oC oD zD
open _root_.NLogN.RS
open _root_.IntMul.HvdH
open _root_.IntMul.OpenAI.RT
open _root_.IntMul.OpenAI.RC
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RCost hiding Ncost c es lam' δ ε κ τ
open _root_.IntMul.OpenAI.R154
variable {E : ℕ} {ix : Ix (7 + E)} {Isym : List Sym} {extM : Fin E → IStmt HS (7 + E)} {n D : ℕ}
  [instS : ∀ i, NeZero (sBD n D i)] [instT : ∀ i, NeZero (tBD n D i)]
set_option maxHeartbeats 8000000

open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

theorem IntMul.OpenAI.R154.P.NLogN.KFM.mul_phase (C : BigCtx ix Isym extM n D) (t : IState HS) (hR : BaseOK t n) (x y : ℕ)
    (hx : x < 2 ^ n) (hy : y < 2 ^ n) (hA : t.G ARGM = [.int (y : ℤ), .int (x : ℤ)])
    (h0 : t.G 0 = []) (hW : t.G pW = []) :
    ∃ (zsZ : List GI) (Z Ux Uy : ((i : Fin (D + 1)) → ZMod (sBD n D i)) → ℂ) (c : ℕ),
      IRuns Isym (kTable extM) (mulP ix) t (((t.upd ARGM []).upd pW []).upd 0 (ints (gflat zsZ)))
        c ∧
      RepPad (pP n) (sBD n D) (tBD n D) zsZ Z ∧ NLogN.KFB.GB (IntMul.OpenAI.R154.P.NLogN.KFM.wU n D) zsZ ∧
      ‖Z - Rperm (sBD n D) (tBD n D) (dftM (sBD n D) (cnj (QA (pP n) (Ux * Uy))))‖ ≤
        EsN n D * hp (pP n) ∧
      ‖Ux - Rperm (sBD n D) (tBD n D)
        (dftM (sBD n D) (fun k => (2 : ℂ)⁻¹ ^ (bP n + 2) * ubar C x k))‖ ≤ EsN n D * hp (pP n) ∧
      ‖Uy - Rperm (sBD n D) (tBD n D)
        (dftM (sBD n D) (fun k => (2 : ℂ)⁻¹ ^ (bP n + 2) * ubar C y k))‖ ≤ EsN n D * hp (pP n) ∧
      (c : ℝ) ≤ kMul C := by sorry
