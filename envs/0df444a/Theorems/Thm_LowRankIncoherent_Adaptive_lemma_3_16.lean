-- Prove2me | Theorems.Thm_LowRankIncoherent_Adaptive_lemma_3_16
-- name    : LowRankIncoherent.Adaptive.lemma_3_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:19:20.774194+00:00
-- url     : https://prove2.me/theorems/f01ce26f-bffe-4886-a94a-eca41f301ebe
-- title:
--   Lemma 3.16 — operator inverse, logarithm and regularization inequalities
-- statement:
--   On positive definite complex matrices in every positive dimension, inversion is operator convex and operator decreasing. The logarithm is operator monotone and operator concave. For every $s>0$, $f_s(X)=X(X+sI)^{-1}$ is also operator monotone and operator concave. In particular, for $0≤t≤1$,
--   $$ (tX+(1-t)Y)^{-1}\preceq tX^{-1}+(1-t)Y^{-1},$$
--   $$\log(tX+(1-t)Y)\succeq t\log X+(1-t)\log Y,$$
--   with the corresponding concavity inequality for $f_s$. The statement contains all six properties, including both monotonicity assertions for logarithm and regularization. The existing proved log-monotonicity reference covers only one clause of this combined target.
--
--   Differences from the source:
--   - encoding: finite complex registers and the source conventions → Fin-indexed matrices, explicit positivity and sample-count domains, and the operational definitions in this mission; reason: coordinate and domain conventions preserve every defined physical instance; no statistical guarantee is assumed
-- source:
--   Aadil Oufkir, Kean Chen, STOC 2027 submission #364 (October 2026), Lemma 3.16, printed p. 32 = PDF p. 32; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/364.pdf

import Definitions.Def_LowRankIncoherent_Adaptive_Algorithm

open Matrix MeasureTheory
open scoped MatrixOrder ComplexOrder ENNReal
noncomputable section

namespace LowRankIncoherent.Adaptive

theorem lemma_3_16 (d : ℕ) (hd : 0 < d) :
    convexOp {X : Input d | X.PosDef} (fun X => X⁻¹) ∧
    (∀ X Y : Input d, X.PosDef → Y.PosDef → LE X Y → LE Y⁻¹ X⁻¹) ∧
    (∀ X Y : Input d, X.PosDef → Y.PosDef → LE X Y → LE (logM X) (logM Y)) ∧
    concaveOp {X : Input d | X.PosDef} logM ∧
    (∀ s : ℝ, 0 < s →
      (∀ X Y : Input d, X.PosDef → Y.PosDef → LE X Y → LE (fs s X) (fs s Y)) ∧
      concaveOp {X : Input d | X.PosDef} (fs s)) := by sorry

end LowRankIncoherent.Adaptive
