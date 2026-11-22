-- Prove2me | Theorems.Thm_GJKKL_Numerics_final_bound
-- name    : GJKKL.Numerics.final_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:32.374964+00:00
-- url     : https://prove2.me/theorems/1fbea300-6f7c-42fc-929a-328c2709c5e2
-- title:
--   Numerics: final bound
-- statement:
--   The Numerics construction uses the final bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Numerics/Final.lean#L30-L99
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Numerics/Final.lean#L30-L99

module
public import Definitions.Def_GJKKL_Numerics_Falling
public import Definitions.Def_GJKKL_Numerics_Final
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Numerics
open Finset Real

theorem GJKKL.Numerics.final_bound {a μ η η4 d P : ℝ} {k1 m : ℕ} (ha : 0 < a) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hη0 : 0 ≤ η) (hημ : η ≤ μ / 2) (hη4 : η ≤ η4) (hη41 : η4 ≤ 1) (hd : 0 ≤ d)
    (hm1 : 1 ≤ m) (hm : (m : ℝ) ≤ (1 - μ) * a) (haμ : 4 ≤ a * μ) (hP : 1 / 2 ≤ P) :
    ((1 - η4) * d / exp k1) ^ m ≤
      P * ((1 - η) * d) ^ m *
        (a ^ m * (∏ i ∈ range m, (1 - (i : ℝ) / a)) ^ (k1 + 1) / m.factorial) := by sorry
