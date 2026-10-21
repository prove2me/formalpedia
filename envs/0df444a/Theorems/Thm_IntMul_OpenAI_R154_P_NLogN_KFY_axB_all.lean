-- Prove2me | Theorems.Thm_IntMul_OpenAI_R154_P_NLogN_KFY_axB_all
-- name    : IntMul.OpenAI.R154.P.NLogN.KFY.axB_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T03:19:38.310432+00:00
-- url     : https://prove2.me/theorems/df978650-2440-4022-b918-0e1178993f02
-- title:
--   axB_all (KFY 13: one axis of the `B₀` pass) (κ = 2⁻¹⁵⁴ constants)
-- statement:
--   **axB_all (KFY 13: one axis of the `B₀` pass)**, at the `frozen-154` constants.
--
--   This is `NLogN.KFY.axB_all` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged) with the constants of §8 replaced by those of the community patch `frozen-154`: $\varepsilon = c = 2^{-51}$, $\lambda' = 1 - 2^{-102}$ ($\tau = 1 - 2^{-50}$ and $\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R154`, and every constant-dependent name lives under `IntMul.OpenAI.R154.P`.
--
--   **Context.** The lemma belongs to the part *KFY 13: one axis of the `B₀` pass*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the frozen-154 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFY.axB_all` (https://prove2.me/theorems/eb760c07-3ff7-449a-bab8-fdb871f8216d).

import Definitions.Def_IntMul_OpenAI_R154_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN ZN bN fsA fsB mN mainA mainB mmN overN srcsN tN ΦN
open _root_.IntMul.OpenAI.R154.P.NLogN.KFY
open _root_.IntMul
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.IntMul.HvdH.Ref hiding bflyB bflyT dcomX dcomY difZ ditZ pmulZ
open _root_.NLogN.GL hiding imE reE rndE
open _root_.NLogN.AX hiding bN
open _root_.NLogN.Rsp hiding BN KN aE cE kE pSt spSt
open _root_.NLogN.KFM (shPad)
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM (bsN)
set_option maxHeartbeats 40000000

open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN ZN bN fsA fsB mN mainA mainB mmN overN srcsN tN ΦN
open _root_.IntMul.OpenAI.R154.P.NLogN.KFY

theorem IntMul.OpenAI.R154.P.NLogN.KFY.axB_all (M : MulSpec) (X : Fin HS) (Kc : ℝ) (hXok : KFM.TrOk X zw zm) (hX0 : X ≠ 0)
    {n : ℕ} (hn : IntMul.OpenAI.Glue.n0 ≤ n) (k : ℕ) (hk : k < IntMul.OpenAI.R154.dP n)
    (u : IState HS) (Xs : List KFB.GI) (R0 RD LP LA LE LD LZ LL LW L55 : List Item)
    (h0 : u.G 0 = ints (KFB.gflat Xs) ++ R0) (hD : u.G NLogN.KFY.dS = .int (IntMul.OpenAI.R154.P.NLogN.KFM.srcN n k : ℤ) :: RD)
    (hP : u.G NLogN.KFY.yP = .int (IntMul.OpenAI.Glue.pP n : ℤ) :: LP) (hA : u.G yA = .int (IntMul.OpenAI.R154.αP n : ℤ) :: LA)
    (hE : u.G KFM.zEl = .int (IntMul.OpenAI.R154.ℓP n : ℤ) :: LE) (hDd : u.G KFM.zD = .int (IntMul.OpenAI.R154.dP n : ℤ) :: LD)
    (hZ : u.G KFM.zDp = .int (IntMul.OpenAI.R154.P.NLogN.KFM.dpN n : ℤ) :: LZ) (hL : u.G yL = .int (IntMul.OpenAI.Glue.LP n : ℤ) :: LL)
    (hW : u.G NLogN.KFY.yW = .int (HvdH.eWidth (IntMul.OpenAI.Glue.pP n) (IntMul.OpenAI.R154.αP n) : ℤ) :: LW)
    (h55 : u.G cX = .int ((IntMul.OpenAI.R154.dP n : ℤ) - k) :: L55)
    (hXs : Xs.length = (List.ofFn (IntMul.OpenAI.R154.P.NLogN.KFM.tB n)).prod) (hGB : KFB.GB (IntMul.OpenAI.Glue.pP n + 2) Xs)
    (hslt : IntMul.OpenAI.R154.P.NLogN.KFM.srcN n k < 2 ^ (IntMul.OpenAI.R154.ℓP n - 1 + bN n k))
    (Bo mm Φ Bacc Q Bq : ℕ) (hM : MulBnd M mm Φ)
    (H : BapHyp (IntMul.OpenAI.Glue.pP n) (IntMul.OpenAI.R154.P.NLogN.KFM.srcN n k) (2 ^ (IntMul.OpenAI.R154.ℓP n - 1 + bN n k)) (IntMul.OpenAI.R154.αP n)
      (2 ^ (IntMul.OpenAI.R154.ℓP n - 1 + bN n k)) (IntMul.OpenAI.Glue.pP n + 2) Bo mm Bacc Q)
    (HT : TabHypB (IntMul.OpenAI.Glue.pP n) (IntMul.OpenAI.R154.P.NLogN.KFM.srcN n k) (2 ^ (IntMul.OpenAI.R154.ℓP n - 1 + bN n k)) (IntMul.OpenAI.R154.αP n) Bq)
    (HQ : AxQA (2 ^ (IntMul.OpenAI.R154.ℓP n - 1 + bN n k)) (2 ^ (IntMul.OpenAI.Glue.LP n - (IntMul.OpenAI.R154.ℓP n - 1 + bN n k)))
      (IntMul.OpenAI.Glue.pP n + 2) Bo Q)
    (A B : ℕ) (hb : AxBndB n A B) :
    (NLogN.KFY.axB X Kc).run u = ((u.upd yS (.int (IntMul.OpenAI.R154.P.NLogN.KFM.srcN n k : ℤ) :: u.G yS)).upd NLogN.KFY.dS RD).upd 0
        (ints (KFB.gflat (stepL ((List.ofFn (IntMul.OpenAI.R154.P.NLogN.KFM.tB n)).rotate k)
          (b0Q (IntMul.OpenAI.Glue.pP n) (IntMul.OpenAI.R154.P.NLogN.KFM.srcN n k) (2 ^ (IntMul.OpenAI.R154.ℓP n - 1 + bN n k)) (IntMul.OpenAI.R154.αP n)) Xs)) ++ R0) ∧
      (NLogN.KFY.axB X Kc).ok M u ∧
      (NLogN.KFY.axB X Kc).cost M u ≤ axBC Kc n (2 ^ (IntMul.OpenAI.R154.ℓP n - 1 + bN n k)) B 30
        (⌈trBound Kc (IntMul.OpenAI.Glue.pP n + 2) (IntMul.OpenAI.R154.ℓP n - 1) (IntMul.OpenAI.R154.dP n) ((List.ofFn (IntMul.OpenAI.R154.P.NLogN.KFM.tB n)).prod)⌉₊ +
          trOver (IntMul.OpenAI.Glue.pP n + 2) (IntMul.OpenAI.R154.ℓP n - 1) (IntMul.OpenAI.R154.dP n))
        (bap0AxCostQ (IntMul.OpenAI.Glue.pP n) (IntMul.OpenAI.R154.P.NLogN.KFM.srcN n k) (2 ^ (IntMul.OpenAI.R154.ℓP n - 1 + bN n k)) (IntMul.OpenAI.R154.αP n)
          (2 ^ (IntMul.OpenAI.Glue.LP n - (IntMul.OpenAI.R154.ℓP n - 1 + bN n k))) mm Φ Bacc Q Bq) := by sorry
