-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFL_linesI_spec
-- name    : IntMul.OpenAI.R129.P.NLogN.KFL.linesI_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:26:28.261926+00:00
-- url     : https://prove2.me/theorems/10121503-bddd-43ac-93fe-76fff1da4d35
-- title:
--   The lines on the canonical layout (κ = 2⁻¹²⁹ constants)
-- statement:
--   **The lines on the canonical layout**, at the `same-network-129` constants.
--
--   This is `NLogN.KFL.linesI_spec` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFL §7: the eight packed lines (22) on the canonical layout*: On the 8-axis geometry `sh8 = [N0,Q,N1,Q,N2,Q,N3,B]` (`Q = 2^{fK}`; slots `x, y, z` = axes
--   1, 3, 5) a `tgtZ` line is one `rotStep` (rotation of slot `z` by `amt l x y`), a `tgtY` line is
--   `swap(3,5); rotStep; swap(3,5)` (Lemma 12 swaps).  `linesI_spec`: running the lines `ls` in
--   order gives `rixT g (ls.foldr (lineP K ρ f))`; for `ls = lines` this is `rixT g (FSc K ρ f)`
--   (`KFLMath`: `FSc` is the pull map of `S0`).  Cost: per line `≤ 2 K_s (V+1) (fK)^τ + cRot`.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFL.linesI_spec` (https://prove2.me/theorems/2be8e020-85ae-4d6e-b1d7-e5a264f82b3e).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 20000
open _root_.NLogN hiding P1
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFL hiding LinesOK SwOK coreCost
open _root_.IntMul.OpenAI.R129.P.NLogN.KFL
open _root_.IntMul
open _root_.NLogN.RS
open _root_.NLogN.KIL hiding Bits Cfg FR St aE cBr cMv cRot cStep negP outR padL rV
open _root_.NLogN.KFD
open _root_.NLogN.KFE
open _root_.NLogN.KFB hiding c1 cPass cZ mvL permL permP rP
open _root_.Butterfly hiding Op
open _root_.AModel hiding hdPos

open _root_.NLogN hiding P1
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFL hiding LinesOK SwOK coreCost
open _root_.IntMul.OpenAI.R129.P.NLogN.KFL

theorem IntMul.OpenAI.R129.P.NLogN.KFL.linesI_spec :
    ∃ T q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∃ Ks : ℝ, 0 ≤ Ks ∧
      ∀ (K ρ f : ℕ), 1 ≤ K → ρ < K → 1 ≤ f →
      ∀ (g : Geo), g.Pos → g.Q = 2 ^ (f * K) →
      ∀ (Bb : ℕ), 2 ≤ Bb → 4 * 2 ^ (f * K) < 2 ^ Bb → zsz (g.V : ℤ) ≤ Bb →
      ∀ (ls : List Line), (∀ l ∈ ls, LineOK l) →
      ∀ (I : List Sym) (t : IState HS) (zs : List ℤ) (R : List Item),
      Bits zs → t.G 0 = ints zs ++ R → zs.length = g.V →
      ∃ c : ℕ, IRuns I l12prog (linesI q K ρ f g ls) t
          (t.upd 0 (ints (rixT g (fun c => ls.foldr (fun l c => lineP K ρ f l c) c) zs) ++ R)) c ∧
        (c : ℝ) ≤ 1 + ls.length * (2 * Ks * ((g.V : ℝ) + 1) * ((f * K : ℕ) : ℝ) ^ (1 - (2 : ℝ)⁻¹ ^ 42)
          + cRotG K f g Bb) := by sorry
