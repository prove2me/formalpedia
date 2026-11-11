-- Prove2me | Theorems.Thm_LowRankIncoherent_Adaptive_corollary_3_20
-- name    : LowRankIncoherent.Adaptive.corollary_3_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:19:22.724376+00:00
-- url     : https://prove2.me/theorems/0de0b883-c6d3-48e5-88b3-9951a8058be9
-- title:
--   Corollary 3.20 — convexity of logarithmic input sensitivity
-- statement:
--   In the standing feasible dimensions fix a rank-at-most-$r$ channel $E$ and $s>0$, and let $A(ρ)=H_s(ρ/2+I_a/(2a))+rI_a$. On the entire density cone, including singular states,
--   $$\log A(tρ_0+(1-t)ρ_1)\preceq t\log A(ρ_0)+(1-t)\log A(ρ_1)\quad(0≤t≤1).$$
--   This is operator convexity of $ρ\mapsto\log A(ρ)$. Positivity of the queried mixture is obtained by construction and does not require positive definiteness of $ρ$.
--
--   Differences from the source:
--   - encoding: finite complex registers and the source conventions → Fin-indexed matrices, explicit positivity and sample-count domains, and the operational definitions in this mission; reason: coordinate and domain conventions preserve every defined physical instance; no statistical guarantee is assumed
-- source:
--   Aadil Oufkir, Kean Chen, STOC 2027 submission #364 (October 2026), Corollary 3.20, printed p. 33 = PDF p. 33; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/364.pdf

import Definitions.Def_LowRankIncoherent_Adaptive_Algorithm

open Matrix MeasureTheory
open scoped MatrixOrder ComplexOrder ENNReal
noncomputable section

namespace LowRankIncoherent.Adaptive

theorem corollary_3_20 {a b r : ℕ} (ha : 0 < a) (hb : 2 ≤ b) (hrpos : 1 ≤ r)
    (hrmax : r ≤ a*b) (hfeasible : a ≤ r*b)
    (E : Map a b) (hE : E ∈ ChanTomoNB.QChan r a b) (s : ℝ) (hs : 0 < s) :
    convexOp {ρ : Input a | State ρ} (fun ρ => logM (Amap E r s ρ)) := by sorry

end LowRankIncoherent.Adaptive
