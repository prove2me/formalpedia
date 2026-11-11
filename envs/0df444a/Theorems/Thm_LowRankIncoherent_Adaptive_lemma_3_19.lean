-- Prove2me | Theorems.Thm_LowRankIncoherent_Adaptive_lemma_3_19
-- name    : LowRankIncoherent.Adaptive.lemma_3_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:19:03.782199+00:00
-- url     : https://prove2.me/theorems/75c7d2d0-513f-4bc1-9a42-3792fd93542f
-- title:
--   Lemma 3.19 — convexity of log of a CP inverse image
-- statement:
--   Let $Φ:L(ℂ^m)\to L(ℂ^a)$ be a completely positive complex-linear map with $Φ(I_m)\succ0$, where both dimensions are positive. Then $Q\mapsto\log Φ(Q^{-1})$ is operator convex on positive definite $Q$:
--   $$\log Φ((tQ_0+(1-t)Q_1)^{-1})\preceq t\log Φ(Q_0^{-1})+(1-t)\log Φ(Q_1^{-1})\quad(0≤t≤1).$$
--   No trace-preservation or unitality is required. This supplies the matrix convexity property used for the input-sensitivity map.
--
--   Differences from the source:
--   - encoding: finite complex registers and the source conventions → Fin-indexed matrices, explicit positivity and sample-count domains, and the operational definitions in this mission; reason: coordinate and domain conventions preserve every defined physical instance; no statistical guarantee is assumed
-- source:
--   Aadil Oufkir, Kean Chen, STOC 2027 submission #364 (October 2026), Lemma 3.19, printed p. 33 = PDF p. 33; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/364.pdf

import Definitions.Def_LowRankIncoherent_Adaptive_Algorithm

open Matrix MeasureTheory
open scoped MatrixOrder ComplexOrder ENNReal
noncomputable section

namespace LowRankIncoherent.Adaptive

theorem lemma_3_19 {m a : ℕ} (hm : 0 < m) (ha : 0 < a) (Φ : Map m a)
    (hCP : CP Φ) (hI : (Φ 1).PosDef) :
    convexOp {Q : Input m | Q.PosDef} (fun Q => logM (Φ Q⁻¹)) := by sorry

end LowRankIncoherent.Adaptive
