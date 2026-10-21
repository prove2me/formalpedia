-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFL_swI_geo
-- name    : IntMul.OpenAI.R129.P.NLogN.KFL.swI_geo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:26:47.151986+00:00
-- url     : https://prove2.me/theorems/4de08576-eb93-4814-8cfd-77af10450e15
-- title:
--   The three swaps on the 8-axis geometry (Q = 2^u): axes 1↔3, 3↔5, 1↔5 are rixT g sw01, rixT g sw12, rixT g… (κ = 2⁻¹²⁹ constants)
-- statement:
--   **The three swaps on the 8-axis geometry (Q = 2^u): axes 1↔3, 3↔5, 1↔5 are rixT g sw01, rixT g sw12, rixT g…**, at the `same-network-129` constants.
--
--   This is `NLogN.KFL.swI_geo` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFL §4: the Lemma 12 swap wrapper*: `swI q vP vG vS u` pushes the four Lemma 12 parameters (`kP, kG, kS, aU`), runs the fine
--   Lemma 12 program `l12F`, and pops them.  `swI_spec`: on any state whose stack 0 is
--   `enc2 xs ++ R` (arbitrary tail `R`, no other hypothesis) it interchanges the two `[2^u]`
--   fields of `binShape Pre G Suf (2^u)` at cost `≤ K (V + 1) u^τ`, `τ = 1 - 2^-42`.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFL.swI_geo` (https://prove2.me/theorems/d7ab15b7-805e-44d0-a547-d78cd98e8663).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
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
open _root_.AModel hiding hdPos
open _root_.AModelL12
open _root_.NetProp7

open _root_.NLogN hiding P1
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFL hiding LinesOK SwOK coreCost
open _root_.IntMul.OpenAI.R129.P.NLogN.KFL

theorem IntMul.OpenAI.R129.P.NLogN.KFL.swI_geo :
    ∃ T q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g : Geo), g.Pos → ∀ u : ℕ, 1 ≤ u → g.Q = 2 ^ u →
      ∀ (I : List Sym) (t : IState HS) (zs : List ℤ) (R : List Item),
      Bits zs → t.G 0 = ints zs ++ R → zs.length = g.V →
      (∃ c : ℕ, IRuns I l12prog (swI q g.N0 g.N1 (vol [g.N2, g.Q, g.N3, g.B]) u) t
          (t.upd 0 (ints (rixT g sw01 zs) ++ R)) c ∧
          (c : ℝ) ≤ K * ((g.V : ℝ) + 1) * (u : ℝ) ^ (1 - (2 : ℝ)⁻¹ ^ 42)) ∧
      (∃ c : ℕ, IRuns I l12prog (swI q (vol [g.N0, g.Q, g.N1]) g.N2 (vol [g.N3, g.B]) u) t
          (t.upd 0 (ints (rixT g sw12 zs) ++ R)) c ∧
          (c : ℝ) ≤ K * ((g.V : ℝ) + 1) * (u : ℝ) ^ (1 - (2 : ℝ)⁻¹ ^ 42)) ∧
      (∃ c : ℕ, IRuns I l12prog (swI q g.N0 (vol [g.N1, g.Q, g.N2]) (vol [g.N3, g.B]) u) t
          (t.upd 0 (ints (rixT g sw02 zs) ++ R)) c ∧
          (c : ℝ) ≤ K * ((g.V : ℝ) + 1) * (u : ℝ) ^ (1 - (2 : ℝ)⁻¹ ^ 42)) := by sorry
