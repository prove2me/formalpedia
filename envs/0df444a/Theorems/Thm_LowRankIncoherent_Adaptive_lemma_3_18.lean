-- Prove2me | Theorems.Thm_LowRankIncoherent_Adaptive_lemma_3_18
-- name    : LowRankIncoherent.Adaptive.lemma_3_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:19:08.697957+00:00
-- url     : https://prove2.me/theorems/8d1b21b9-19c4-45a4-89c6-60fd9d0b477c
-- title:
--   Lemma 3.18 — trace budget for input sensitivity
-- statement:
--   In the standing feasible dimensions let $E$ have Kraus rank at most $r$, let $s>0$, and put $σ(ρ)=ρ/2+I_a/(2a)$ and $A(ρ)=H_s(σ(ρ))+rI_a$. Every state $ρ$ satisfies
--   $$\operatorname{tr}(ρA(ρ))≤3r.$$
--   This trace budget concerns all input states, including singular ones, and is used in the input-selection guarantee.
--
--   Differences from the source:
--   - encoding: finite complex registers and the source conventions → Fin-indexed matrices, explicit positivity and sample-count domains, and the operational definitions in this mission; reason: coordinate and domain conventions preserve every defined physical instance; no statistical guarantee is assumed
-- source:
--   Aadil Oufkir, Kean Chen, STOC 2027 submission #364 (October 2026), Lemma 3.18, printed p. 32 = PDF p. 32; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/364.pdf

import Definitions.Def_LowRankIncoherent_Adaptive_Algorithm

open Matrix MeasureTheory
open scoped MatrixOrder ComplexOrder ENNReal
noncomputable section

namespace LowRankIncoherent.Adaptive

theorem lemma_3_18 {a b r : ℕ} (ha : 0 < a) (hb : 2 ≤ b) (hrpos : 1 ≤ r)
    (hrmax : r ≤ a*b) (hfeasible : a ≤ r*b)
    (E : Map a b) (hE : E ∈ ChanTomoNB.QChan r a b)
    (s : ℝ) (hs : 0 < s) (ρ : Input a) (hρ : State ρ) :
    rt (ρ * Amap E r s ρ) ≤ 3*r := by sorry

end LowRankIncoherent.Adaptive
