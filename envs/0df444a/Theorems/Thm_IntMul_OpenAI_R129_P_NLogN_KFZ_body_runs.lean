-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFZ_body_runs
-- name    : IntMul.OpenAI.R129.P.NLogN.KFZ.body_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:54.926174+00:00
-- url     : https://prove2.me/theorems/5193315e-601b-4f36-9e9e-0a507ad30947
-- title:
--   body_runs (KFZ Full: the whole chirp procedure body) (κ = 2⁻¹²⁹ constants)
-- statement:
--   **body_runs (KFZ Full: the whole chirp procedure body)**, at the `same-network-129` constants.
--
--   This is `NLogN.KFZ.body_runs` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFZ Full: the whole chirp procedure body*: `body j d18 = setupP; T1; …; T7; wP setC (PP j d18); popsL regL`.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFZ.body_runs` (https://prove2.me/theorems/9bec3fb3-f396-4102-9154-c6f3f99a29e0).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open _root_.NLogN hiding St T1 T2 T3 T4 T5 T6 T7 tE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFZ hiding BN ChirpNeedR bitN bsN hN length_bsN length_ssN ssN σN
open _root_.IntMul.OpenAI.R129.P.NLogN.KFZ
open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR St aE cBody negP outR padL pushF pushes
open _root_.NLogN.KFB hiding permL permP qA qT
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DE DescRegs ErC EsN LRegs LineNeed NcN P18IL PhiNeed QRegs SwapNeed TrRegs TransNeed bLn baseSt bigP bitE bsN cLineU cPhiU chirpGN descChirpN descLineN descPhiN dpN eB eN fmB gapR gconj kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm liftL lineG muN parC parQV phiG prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD sumB tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R129
variable {E : ℕ} (ext : Fin E → IStmt HS (7 + E)) {I : List Sym} (s : IState HS)

open _root_.NLogN hiding St T1 T2 T3 T4 T5 T6 T7 tE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFZ hiding BN ChirpNeedR bitN bsN hN length_bsN length_ssN ssN σN
open _root_.IntMul.OpenAI.R129.P.NLogN.KFZ

theorem IntMul.OpenAI.R129.P.NLogN.KFZ.body_runs (j : Fin (7 + E)) (d18 : Fin HS) (hd0 : d18 ≠ 0) {n : ℕ} (hn : IntMul.OpenAI.Glue.n0 ≤ n)
    {D p h σ K α B : ℕ} (hB : RB p h (D + 1) σ K B) (hD : D + 1 = IntMul.OpenAI.R129.dP n)
    (hdp : D + 1 - σ = dpN n) (hr : 2 ^ (h + 1) = IntMul.OpenAI.R129.rP n) (hK : K = KP n) (hl : h + 1 = ℓP n)
    (hb : p / 6 = bP n) (hp : p = pP n) (Bd : ℕ)
    (hBd : ∀ x ∈ desc18 (pP n) (ℓP n) (KP n) (tsN n), zsz x ≤ Bd)
    (sv t : Fin (D + 1) → ℕ) [∀ i, NeZero (t i)] (hst : ∀ i, sv i ≤ t i) (htp : ∀ i, 0 < t i)
    (hT : ∀ i, t i ≤ 2 ^ (h + 1)) (htl : t (Fin.last D) = 2 ^ (h + 1))
    (hprod : ∏ i, t i = 2 ^ ((D + 1) * h + σ))
    (hM : 2 ^ ((D + 1) * h + σ - (h + 1)) = ∏ i : Fin D, t i.castSucc)
    (bs ss : List ℕ) (hbl : bs.length = D + 1) (hsl : ss.length = D + 1) (hb1 : ∀ b ∈ bs, b ≤ 1)
    (hstl : ∀ (i : ℕ) (hi : i < D + 1), ss[i]'(by omega) ≤ 2 ^ (h + bs[i]'(by omega)))
    (hσ : bs.sum = σ) (hsB : NLogN.KFZ.eS h bs (D + 1) + h + 6 ≤ B) (hdB : D + 1 + 2 ≤ B)
    (hKB : zsz (K : ℤ) ≤ B) (hpB : zsz (p : ℤ) ≤ B) (hαB : zsz (α : ℤ) ≤ B)
    (hdesc : descA 1 (axD h bs ss) ++ [(2 * 2 ^ NLogN.KFZ.eS h bs (D + 1) : ℤ)] = descT sv t)
    (f : Fin HS → List ℤ) (hf : EmptyEx f)
    (hc : f NLogN.KFZ.cS = (K : ℤ) :: (p : ℤ) :: (α : ℤ) :: (h : ℤ) :: ((D + 1 : ℕ) : ℤ) ::
      (NLogN.KFZ.zl bs ++ NLogN.KFZ.zl ss))
    (xs : List GI) (l : List ℤ) (h0 : f 0 = gflat xs ++ l) (hxs : xs.length = ∏ i, t i)
    (gx : NLogN.KFB.GB (p + 2) xs) (zh : List GI) (hzh : zh.length = ∏ i, t i) (gh : NLogN.KFB.GB (p + 2) zh)
    (gU : NLogN.KFB.GB (p + 2) (List.zipWith (gmulT p) xs (aLz p h D sv t)))
    (gG : NLogN.KFB.GB (p + 2) (zGz p h D sv t xs)) (gF : NLogN.KFB.GB (p + 2) (zFz p h D sv t))
    (gV : NLogN.KFB.GB (p + 2) (List.zipWith (gmulT p) zh (iLz p h D t))) (c18 : ℕ)
    (hcall : IRuns I (kTable ext) (.call j)
      (NLogN.KIL.encK (bgS s (preM (FC f p h D σ K sv t (gflat xs ++ l)) (zFz p h D sv t)
          (zGz p h D sv t xs) l) d18 l)
        (NLogN.KFZ.fC d18 (gflat (zFz p h D sv t) ++ gflat (zGz p h D sv t xs) ++ [])
          (desc18 (pP n) (ℓP n) (KP n) (tsN n))))
      (NLogN.KIL.encK (bgS s (preM (FC f p h D σ K sv t (gflat xs ++ l)) (zFz p h D sv t)
          (zGz p h D sv t xs) l) d18 l)
        (Function.update (NLogN.KFZ.fC d18 (gflat (zFz p h D sv t) ++ gflat (zGz p h D sv t xs) ++ [])
          (desc18 (pP n) (ℓP n) (KP n) (tsN n))) 0 (gflat zh ++ []))) c18) :
    IRuns I (kTable ext) (body j d18) (NLogN.KIL.encK s f)
      (NLogN.KIL.encK s (Function.update f 0 (gflat (yz p h D sv t zh) ++ l)))
      (c18 + NLogN.KFZ.cBody B Bd (bP n) (desc18 (pP n) (ℓP n) (KP n) (tsN n)).length p h D σ sv t) := by sorry
