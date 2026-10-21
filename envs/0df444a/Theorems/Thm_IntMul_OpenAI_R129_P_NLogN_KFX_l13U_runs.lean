-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFX_l13U_runs
-- name    : IntMul.OpenAI.R129.P.NLogN.KFX.l13U_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:28.906265+00:00
-- url     : https://prove2.me/theorems/e4425447-264b-4292-b338-0bc985f58232
-- title:
--   Lemma 13, register-driven: the denotation and the cost pieces (KFL.l13_runs for l13U) (κ = 2⁻¹²⁹ constants)
-- statement:
--   **Lemma 13, register-driven: the denotation and the cost pieces (KFL.l13_runs for l13U)**, at the `same-network-129` constants.
--
--   This is `NLogN.KFX.l13U_runs` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFX §4: the register-driven Lemma 13 core*: The fixed code `l13U q` is `KFL.l13code` with every size-dependent literal read from the
--   *master registers* (`MReg`): `w, 2·M·R` on `1, 6` (for `toBitsU`/`fromBitsU`), the swap flags on
--   `11, 12`, and `Q = 2^{fK}, B = R·2(w+1), 2^ρ, gx, N0, N1, N2, N3, A = zsz V, 2^K` on
--   `13, 15, 16, 17, 18, 19, 46, 47, 48, 49`, `f, K` on `36, 37`.  The slot swaps `preL px py` are
--   realized by two optional swaps (`optA`: swap `0` or `2` by the flag on `11`, `optB`: swap `1` by
--   the flag on `12`).  **`l13U_runs`** is `KFL.l13_runs` for this code.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFX.l13U_runs` (https://prove2.me/theorems/e8cbb893-b3f8-46a4-8e5b-203c5a9c6bd6).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 20000
open _root_.NLogN
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFX hiding L13U SwEOK
open _root_.IntMul.OpenAI.R129.P.NLogN.KFX
open _root_.IntMul
open _root_.NLogN.RS
open _root_.NLogN.KIL hiding Cfg FR St aE negP outR padL zB
open _root_.NLogN.KFD
open _root_.NLogN.KFE
open _root_.NLogN.KFB hiding cZ permL permP
open _root_.NLogN.KFL hiding LinesOK P1 SwOK cZ coreCost rX
open _root_.IntMul.OpenAI.R129.P.NLogN.KFL
open _root_.NLogN.KFW hiding RowU RowUP cBody cCL cChain cLowP cLowPart cTot cbW clF coefF eBp padL vE
open _root_.IntMul.OpenAI.R129.P.NLogN.KFW
open _root_.NLogN.KFH
open _root_.AModel hiding hdPos
open _root_.Butterfly hiding Op
variable {N0 N1 N2 N3 K f ρ R w : ℕ} {px py : Fin 3} {t : IState HS}
set_option maxHeartbeats 2000000

open _root_.NLogN
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFX hiding L13U SwEOK
open _root_.IntMul.OpenAI.R129.P.NLogN.KFX

theorem IntMul.OpenAI.R129.P.NLogN.KFX.l13U_runs {q : ℕ} {Ksw Kc : ℝ} (hKsw : 0 ≤ Ksw) (hKc : 0 ≤ Kc) (HSw : SwEOK q Ksw)
    (HC : CorrUOK Kc) (hne : px ≠ py) (hK6 : 6 ≤ K) (hp : PPos N0 N1 N2 N3 K f ρ R)
    (I : List Sym) (t : IState HS) (hA : Agree (σMR N0 N1 N2 N3 K f ρ R w px py) t)
    (zs : List GI) (R0 : List Item) (h0 : t.G 0 = ints (gflat zs) ++ R0)
    (hl : zs.length = vol (rect N0 N1 N2 N3 (f * K)) * R) (hGB : NLogN.KFB.GB w zs) :
    ∃ c, IRuns I l12prog (l13U q) t
        (t.upd 0 (ints (gflat (permRecs (rect N0 N1 N2 N3 (f * K))
          (rowAddAddr K ρ f px py) R zs)) ++ R0)) c ∧
      (c : ℝ) ≤ 2000 * (cTo (2 * (vol (rect N0 N1 N2 N3 (f * K)) * R)) w : ℝ) +
        4 * (26 + Ksw * (((NLogN.KFX.gB N0 N1 N2 N3 K f R w).V : ℝ) + 1) *
          ((f * K : ℕ) : ℝ) ^ (1 - (2 : ℝ)⁻¹ ^ 42)) +
        (400 * IntMul.OpenAI.R129.P.NLogN.KFL.coreCost Ksw Kc K ρ f (NLogN.KFX.gB N0 N1 N2 N3 K f R w) +
          10 ^ 10 * (((zsz ((NLogN.KFX.gB N0 N1 N2 N3 K f R w).V : ℤ) + 3 : ℕ) : ℝ) + 2) ^ 2) +
        2000 * (cFrom (2 * (vol (rect N0 N1 N2 N3 (f * K)) * R)) w : ℝ) := by sorry
