-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFY_axA_all
-- name    : IntMul.OpenAI.R129.P.NLogN.KFY.axA_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:36.696693+00:00
-- url     : https://prove2.me/theorems/4066eb8d-6336-4365-a9b5-7d9b58a616ab
-- title:
--   axA_all (KFY 12: one axis of the `A` pass) (κ = 2⁻¹²⁹ constants)
-- statement:
--   **axA_all (KFY 12: one axis of the `A` pass)**, at the `same-network-129` constants.
--
--   This is `NLogN.KFY.axA_all` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFY 12: one axis of the `A` pass*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFY.axA_all` (https://prove2.me/theorems/726a202e-737e-4e68-8e1d-a7b922da24fb).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN TrHyp ZN axA axB bN fsA fsB mN mainA mainB mmN overN progA progB srcsN tN trBlk trBound trC trPrc ΦN
open _root_.IntMul.OpenAI.R129.P.NLogN.KFY
open _root_.IntMul
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.IntMul.HvdH.Ref hiding bflyB bflyT dcomX dcomY difZ ditZ pmulZ
open _root_.NLogN.GL hiding imE reE rndE
open _root_.NLogN.AX hiding bN
open _root_.NLogN.Rsp hiding BN KN aE cE kE pSt spSt
open _root_.NLogN.KFM (shPad)
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM (bsN)
set_option maxHeartbeats 20000000

open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN TrHyp ZN axA axB bN fsA fsB mN mainA mainB mmN overN progA progB srcsN tN trBlk trBound trC trPrc ΦN
open _root_.IntMul.OpenAI.R129.P.NLogN.KFY

theorem IntMul.OpenAI.R129.P.NLogN.KFY.axA_all (M : MulSpec) (X : Fin HS) (Kc : ℝ) (hXok : KFM.TrOk X zw zm) (hX0 : X ≠ 0)
    {n : ℕ} (hn : IntMul.OpenAI.Glue.n0 ≤ n) (k : ℕ) (hk : k < IntMul.OpenAI.R129.dP n)
    (u : IState HS) (Xs : List KFB.GI) (R0 RD LP LA LE LD LZ LL LW L55 : List Item)
    (h0 : u.G 0 = ints (KFB.gflat Xs) ++ R0) (hD : u.G NLogN.KFY.dS = .int (IntMul.OpenAI.R129.P.NLogN.KFM.srcN n k : ℤ) :: RD)
    (hP : u.G NLogN.KFY.yP = .int (IntMul.OpenAI.Glue.pP n : ℤ) :: LP) (hA : u.G yA = .int (IntMul.OpenAI.R129.αP n : ℤ) :: LA)
    (hE : u.G KFM.zEl = .int (IntMul.OpenAI.R129.ℓP n : ℤ) :: LE) (hDd : u.G KFM.zD = .int (IntMul.OpenAI.R129.dP n : ℤ) :: LD)
    (hZ : u.G KFM.zDp = .int (IntMul.OpenAI.R129.P.NLogN.KFM.dpN n : ℤ) :: LZ) (hL : u.G yL = .int (IntMul.OpenAI.Glue.LP n : ℤ) :: LL)
    (hW : u.G NLogN.KFY.yW = .int (HvdH.sWidth (IntMul.OpenAI.Glue.pP n) (IntMul.OpenAI.R129.αP n) : ℤ) :: LW)
    (h55 : u.G cX = .int ((IntMul.OpenAI.R129.dP n : ℤ) - k) :: L55)
    (hXs : Xs.length = (List.ofFn (IntMul.OpenAI.R129.P.NLogN.KFM.tB n)).prod) (hGB : KFB.GB (IntMul.OpenAI.Glue.pP n + 2) Xs)
    (Bo mm Φ Bacc Q Bq : ℕ) (hM : MulBnd M mm Φ)
    (H : SapHyp (IntMul.OpenAI.Glue.pP n) (IntMul.OpenAI.R129.P.NLogN.KFM.srcN n k) (2 ^ (IntMul.OpenAI.R129.ℓP n - 1 + IntMul.OpenAI.R129.P.NLogN.KFY.bN n k)) (IntMul.OpenAI.R129.αP n)
      (IntMul.OpenAI.Glue.pP n + 2) Bo mm Bacc Q)
    (HT : TabHyp (IntMul.OpenAI.Glue.pP n) (IntMul.OpenAI.R129.P.NLogN.KFM.srcN n k) (2 ^ (IntMul.OpenAI.R129.ℓP n - 1 + IntMul.OpenAI.R129.P.NLogN.KFY.bN n k)) (IntMul.OpenAI.R129.αP n) Bq)
    (HQ : AxQA (2 ^ (IntMul.OpenAI.R129.ℓP n - 1 + IntMul.OpenAI.R129.P.NLogN.KFY.bN n k)) (2 ^ (IntMul.OpenAI.Glue.LP n - (IntMul.OpenAI.R129.ℓP n - 1 + IntMul.OpenAI.R129.P.NLogN.KFY.bN n k)))
      (IntMul.OpenAI.Glue.pP n + 2) Bo Q)
    (A B : ℕ) (hb : AxBnd n A B) :
    (axA X Kc).run u = ((u.upd yS (.int (IntMul.OpenAI.R129.P.NLogN.KFM.srcN n k : ℤ) :: u.G yS)).upd NLogN.KFY.dS RD).upd 0
        (ints (KFB.gflat (stepL ((List.ofFn (IntMul.OpenAI.R129.P.NLogN.KFM.tB n)).rotate k)
          (sapL (IntMul.OpenAI.Glue.pP n) (IntMul.OpenAI.R129.P.NLogN.KFM.srcN n k) (2 ^ (IntMul.OpenAI.R129.ℓP n - 1 + IntMul.OpenAI.R129.P.NLogN.KFY.bN n k)) (IntMul.OpenAI.R129.αP n)) Xs)) ++ R0) ∧
      (axA X Kc).ok M u ∧
      (axA X Kc).cost M u ≤ axAC Kc n k B 20
        (⌈trBound Kc (IntMul.OpenAI.Glue.pP n + 2) (IntMul.OpenAI.R129.ℓP n - 1) (IntMul.OpenAI.R129.dP n) ((List.ofFn (IntMul.OpenAI.R129.P.NLogN.KFM.tB n)).prod)⌉₊ +
          trOver (IntMul.OpenAI.Glue.pP n + 2) (IntMul.OpenAI.R129.ℓP n - 1) (IntMul.OpenAI.R129.dP n))
        (sapAxCostQ (IntMul.OpenAI.Glue.pP n) (IntMul.OpenAI.R129.P.NLogN.KFM.srcN n k) (2 ^ (IntMul.OpenAI.R129.ℓP n - 1 + IntMul.OpenAI.R129.P.NLogN.KFY.bN n k)) (IntMul.OpenAI.R129.αP n)
          (2 ^ (IntMul.OpenAI.Glue.LP n - (IntMul.OpenAI.R129.ℓP n - 1 + IntMul.OpenAI.R129.P.NLogN.KFY.bN n k))) mm Φ Bacc Q Bq) := by sorry
