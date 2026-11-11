-- Prove2me | Theorems.Thm_GaussPolyReg_Approx_lemma_A_3
-- name    : GaussPolyReg.Approx.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:48.305212+00:00
-- url     : https://prove2.me/theorems/8b83ba11-6691-4091-82de-7ee52f0fd51d
-- title:
--   Lemma A.3 — Gaussian hypercontractive inequality
-- statement:
--   Let $d\in\mathbb N$, $p\in H_{\le d}(X)$, and let $q\ge2$ be real. Then
--
--   $$\|p\|_q\le(q-1)^{d/2}\|p\|_2.$$
--
--   The $q$-norm is the extended nonnegative Lᵠ norm. The result applies to the closed chaos over countably many Gaussian coordinates, including infinite Hermite expansions. It supplies integrability estimates for all subsequent moment statements.
--
--   Differences from the source:
--   - encoding: functions of the original Gaussian variables, with the closed spans fixed in §2 → L² almost-everywhere classes on the product Gaussian space indexed by ℕ; index n uses coordinates 0 through n−1; reason: reindexing X₁,X₂,… changes no random variable or closed-span instance
--   - encoding: Lᵠ norm → extended nonnegative eLpNorm and a finite real right-hand side; reason: the inequality implies finiteness and cannot hold because a Bochner integral defaulted to zero
-- source:
--   Chris Jones, Regularity lemma for Gaussian polynomials, STOC 2027 submission #1637 (October 2026), Lemma A.3, p. 17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1637.pdf

import Mathlib
import Definitions.Def_GaussPolyReg_Approx_Chaos

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace GaussPolyReg.Approx

theorem lemma_A_3 (d : ℕ) (p : Original) (hp : p ∈ chaosLE d)
    (q : ℝ) (hq : 2 ≤ q) :
    eLpNorm (fun x => p x) (ENNReal.ofReal q) (gaussianProduct ℕ) ≤
      ENNReal.ofReal ((q-1) ^ ((d : ℝ)/2)) * ENNReal.ofReal ‖p‖ := by sorry

end GaussPolyReg.Approx
