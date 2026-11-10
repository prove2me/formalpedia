-- Prove2me | Theorems.Thm_GEPPGrowth_Main_gepp_regular
-- name    : GEPPGrowth.Main.gepp_regular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:38:03.880804+00:00
-- url     : https://prove2.me/theorems/56aed026-bc56-4b5d-a1b6-f552d930a929
-- title:
--   GEPP measurability, null exceptional inputs, and pivot tie agreement
-- statement:
--   Let $n\ge1$ and let $A$ have the full product standard real Gaussian matrix law. The exact GEPP output $U(A)$ and its growth factor are measurable. Almost surely,
--
--   $$\det A\ne0,\quad\|A\|_{\max}\ne0,$$
--
--   all pivots are nonzero, the remaining entries of every pivot column have distinct absolute values, and every admissible pivot rule produces the same final $U(A)$ as the smallest-index implementation. Admissibility means choosing an eligible row of largest absolute entry at every step.
--
--   These explicit obligations justify the total extension and the tie convention in the algorithm definitions. They impose no conditioning or good-event assumption on the input law.
--
--   Differences from the source:
--   - encoding: GEPP on nonsingular Gaussian inputs with arbitrary pivot ties → measurable total functions with almost-sure regularity and equality for every admissible pivot rule; reason: records the null-set and convention equivalence obligations implicit in the source
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), §2.1, printed pp.2–3, PDF pp.3–4; Definition 2.1, printed p.4, PDF p.5 (well-posedness obligations)

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- §2.1 and Definition 2.1: null-set and tie-convention obligations; no regularity hypothesis is imposed on the input law. -/
theorem gepp_regular (n : ℕ) (hn : 0 < n) :
    Measurable (upper (n := n)) ∧ Measurable (growth (n := n)) ∧
    (∀ᵐ A ∂(GaussianMatrix.gaussianMatrix n n),
      A.det ≠ 0 ∧ maxEntry A ≠ 0 ∧ Regular A ∧
      ∀ p : Fin n → Mat n → Fin n, IsPivotRule p → upperWith p A = upper A) := by sorry

end GEPPGrowth.Main
