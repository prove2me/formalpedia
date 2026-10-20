-- Prove2me | Theorems.Thm_IntMul_OpenAI_R154_P_NLogN_KFY_pass_all
-- name    : IntMul.OpenAI.R154.P.NLogN.KFY.pass_all
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-20T03:21:42.250015+00:00
-- url     : https://prove2.me/theorems/1286c94e-cc6f-45ea-bd6f-12703e36bf9a
-- title:
--   pass_all (KFY 15: a whole line pass (generic in the width program and the axis body)) (κ = 2⁻¹⁵⁴ constants)
-- statement:
--   **pass_all (KFY 15: a whole line pass (generic in the width program and the axis body))**, at the `frozen-154` constants.
--
--   This is `NLogN.KFY.pass_all` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged) with the constants of §8 replaced by those of the community patch `frozen-154`: $\varepsilon = c = 2^{-51}$, $\lambda' = 1 - 2^{-102}$ ($\tau = 1 - 2^{-50}$ and $\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R154`, and every constant-dependent name lives under `IntMul.OpenAI.R154.P`.
--
--   **Context.** The lemma belongs to the part *KFY 15: a whole line pass (generic in the width program and the axis body)*: `passP wP ax = rs (proP; wP) ; rep cX (reg zD) ax ; rs epiP`.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the frozen-154 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFY.pass_all` (https://prove2.me/theorems/d2356ee9-aa44-43e1-a06c-633b9f23e673).

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
set_option maxHeartbeats 8000000

open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN ZN bN fsA fsB mN mainA mainB mmN overN srcsN tN ΦN
open _root_.IntMul.OpenAI.R154.P.NLogN.KFY

theorem IntMul.OpenAI.R154.P.NLogN.KFY.pass_all (M : MulSpec) (wP : RS) (ax : RM) (hw : cX ∉ ax.writes)
    {n : ℕ} (hn : IntMul.OpenAI.Glue.n0 ≤ n) (s : IState HS) (zs : List KFB.GI) (R0 R : List Item)
    (h0 : s.G 0 = ints (KFB.gflat zs) ++ R0)
    (hD : s.G NLogN.KFY.dS = ints (NLogN.KFY.descL (IntMul.OpenAI.Glue.pP n) (IntMul.OpenAI.R154.αP n) (IntMul.OpenAI.R154.ℓP n - 1) (IntMul.OpenAI.R154.dP n) (IntMul.OpenAI.R154.P.NLogN.KFM.dpN n)
      (srcsN n)) ++ R)
    (w Cw : ℕ) (hwP : ∀ (t : IState HS) (LP LA : List Item), t.G NLogN.KFY.yP = .int (IntMul.OpenAI.Glue.pP n : ℤ) :: LP →
      t.G yA = .int (IntMul.OpenAI.R154.αP n : ℤ) :: LA → RSAll wP t (t.upd NLogN.KFY.yW (.int (w : ℤ) :: t.G NLogN.KFY.yW)) Cw)
    (fs : ℕ → List KFB.GI → List KFB.GI) (P : List KFB.GI → Prop) (hP0 : P zs)
    (hPstep : ∀ k < IntMul.OpenAI.R154.dP n, ∀ X, P X → P (stepL ((List.ofFn (IntMul.OpenAI.R154.P.NLogN.KFM.tB n)).rotate k) (fs k) X))
    (C : ℕ)
    (Hstep : ∀ k < IntMul.OpenAI.R154.dP n, ∀ (u : IState HS) (Xs : List KFB.GI)
      (RD LP LA LE LD LZ LL LW L55 : List Item),
      u.G 0 = ints (KFB.gflat Xs) ++ R0 → u.G NLogN.KFY.dS = .int (IntMul.OpenAI.R154.P.NLogN.KFM.srcN n k : ℤ) :: RD →
      u.G NLogN.KFY.yP = .int (IntMul.OpenAI.Glue.pP n : ℤ) :: LP → u.G yA = .int (IntMul.OpenAI.R154.αP n : ℤ) :: LA →
      u.G KFM.zEl = .int (IntMul.OpenAI.R154.ℓP n : ℤ) :: LE → u.G KFM.zD = .int (IntMul.OpenAI.R154.dP n : ℤ) :: LD →
      u.G KFM.zDp = .int (IntMul.OpenAI.R154.P.NLogN.KFM.dpN n : ℤ) :: LZ → u.G yL = .int (IntMul.OpenAI.Glue.LP n : ℤ) :: LL →
      u.G NLogN.KFY.yW = .int (w : ℤ) :: LW → u.G cX = .int ((IntMul.OpenAI.R154.dP n : ℤ) - k) :: L55 → P Xs →
      ax.run u = ((u.upd yS (.int (IntMul.OpenAI.R154.P.NLogN.KFM.srcN n k : ℤ) :: u.G yS)).upd NLogN.KFY.dS RD).upd 0
          (ints (KFB.gflat (stepL ((List.ofFn (IntMul.OpenAI.R154.P.NLogN.KFM.tB n)).rotate k) (fs k) Xs)) ++ R0) ∧
        ax.ok M u ∧ ax.cost M u ≤ C)
    (A B : ℕ) (hEnv : KFM.CostEnv A B) (hpA : IntMul.OpenAI.Glue.pP n ≤ A) (hαA : IntMul.OpenAI.R154.αP n ≤ A)
    (hlA : IntMul.OpenAI.R154.ℓP n ≤ A) (hdlA : IntMul.OpenAI.R154.dP n * IntMul.OpenAI.R154.ℓP n ≤ A) (hwA : w ≤ A) (hLA : IntMul.OpenAI.Glue.LP n ≤ A)
    (hsrc : ∀ x ∈ srcsN n, zsz x ≤ B) :
    (passP wP ax).run s = s.upd 0 (ints (KFB.gflat (NLogN.KFY.iterL (List.ofFn (IntMul.OpenAI.R154.P.NLogN.KFM.tB n)) fs (IntMul.OpenAI.R154.dP n) zs))
        ++ R0) ∧
      (passP wP ax).ok M s ∧ (passP wP ax).cost M s ≤ passC (IntMul.OpenAI.R154.dP n) B Cw C := by sorry
