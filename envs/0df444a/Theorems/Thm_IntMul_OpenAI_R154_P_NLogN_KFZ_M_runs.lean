-- Prove2me | Theorems.Thm_IntMul_OpenAI_R154_P_NLogN_KFZ_M_runs
-- name    : IntMul.OpenAI.R154.P.NLogN.KFZ.M_runs
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-20T03:21:44.006155+00:00
-- url     : https://prove2.me/theorems/10cd692a-d1bf-476e-9ca8-a513cec2f862
-- title:
--   M_runs (KFZ Call: the Prop 18 call inside the chirp procedure) (κ = 2⁻¹⁵⁴ constants)
-- statement:
--   **M_runs (KFZ Call: the Prop 18 call inside the chirp procedure)**, at the `frozen-154` constants.
--
--   This is `NLogN.KFZ.M_runs` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged) with the constants of §8 replaced by those of the community patch `frozen-154`: $\varepsilon = c = 2^{-51}$, $\lambda' = 1 - 2^{-102}$ ($\tau = 1 - 2^{-50}$ and $\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R154`, and every constant-dependent name lives under `IntMul.OpenAI.R154.P`.
--
--   **Context.** The lemma belongs to the part *KFZ Call: the Prop 18 call inside the chirp procedure*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the frozen-154 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFZ.M_runs` (https://prove2.me/theorems/de914e66-8bbe-4ef7-9aa4-694413ad5747).

import Definitions.Def_IntMul_OpenAI_R154_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open _root_.NLogN hiding St T1 T2 T3 T4 T5 T6 T7 tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFZ hiding BN ChirpNeedR bitN bsN hN length_bsN length_ssN ssN σN
open _root_.IntMul.OpenAI.R154.P.NLogN.KFZ
open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR St aE cBody negP outR padL pushF pushes
open _root_.NLogN.KFB hiding permL permP qA qT
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DE DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bitE bsN cLineU chirpGN descChirpN descLineN descPhiN dpN eB eN fmB gapR gconj kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm liftL lineG muN parC parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD sumB tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
variable {E : ℕ} {I : List Sym} {iprog : Fin (7 + E) → IStmt HS (7 + E)}

open _root_.NLogN hiding St T1 T2 T3 T4 T5 T6 T7 tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFZ hiding BN ChirpNeedR bitN bsN hN length_bsN length_ssN ssN σN
open _root_.IntMul.OpenAI.R154.P.NLogN.KFZ

theorem IntMul.OpenAI.R154.P.NLogN.KFZ.M_runs (j : Fin (7 + E)) (d18 : Fin HS) (hd0 : d18 ≠ 0) {n : ℕ} (hn : IntMul.OpenAI.Glue.n0 ≤ n)
    {p h d σ K B : ℕ} (hB : RB p h d σ K B) (hd : d = IntMul.OpenAI.R154.dP n) (hdp : d - σ = dpN n)
    (hr : 2 ^ (h + 1) = IntMul.OpenAI.R154.rP n) (hK : K = KP n) (hl : h + 1 = ℓP n) (hb : p / 6 = bP n)
    (hp : p = pP n) (Bd : ℕ) (hBd : ∀ x ∈ desc18 (pP n) (ℓP n) (KP n) (tsN n), zsz x ≤ Bd)
    (s : IState HS) (G : Fin HS → List ℤ) (hR : Regs G p h d σ K) (ZF ZG : List GI) (l : List ℤ)
    (h0 : G 0 = gflat ZF ++ gflat ZG ++ l) (hX : G (X18 d18) = [])
    (zh : List GI) (c : ℕ)
    (hcall : IRuns I iprog (.call j)
      (NLogN.KIL.encK (bgS s G d18 l) (NLogN.KFZ.fC d18 (gflat ZF ++ gflat ZG ++ [])
        (desc18 (pP n) (ℓP n) (KP n) (tsN n))))
      (NLogN.KIL.encK (bgS s G d18 l) (Function.update (NLogN.KFZ.fC d18 (gflat ZF ++ gflat ZG ++ [])
        (desc18 (pP n) (ℓP n) (KP n) (tsN n))) 0 (gflat zh ++ []))) c) :
    IRuns I iprog (Mcall j d18) (NLogN.KIL.encK s G) (NLogN.KIL.encK s (Function.update G 0 (gflat zh ++ l)))
      (c + cM B Bd (bP n) (desc18 (pP n) (ℓP n) (KP n) (tsN n)).length) := by sorry
