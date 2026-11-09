-- Prove2me | Theorems.Thm_NetworkEquilibriumCLS_LinearNash_quadratic_kkt_rounding
-- name    : NetworkEquilibriumCLS.LinearNash.quadratic_kkt_rounding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:26.819673+00:00
-- url     : https://prove2.me/theorems/40bb5bb2-91e7-47bc-a6b6-761ea089555b
-- title:
--   Lemma 2.2 — polynomial-time rounding of approximate KKT points
-- statement:
--   For every rational quadratic p in a positive dimension m, there are uniform polynomial-time routines choosing a positive rational tolerance ε(p) and decoding any rational ε(p)-KKT point to an exact rational KKT point:
--
--   $$\varepsilon(p)>0,\qquad z\text{ is }\varepsilon(p)\text{-KKT}\ \Longrightarrow\ D(p,z)\text{ is exact KKT for }p.$$
--
--   The tolerance is computed from the input alone, and the decoder reads both the original input and the approximate point. Both runtime bounds are uniform in binary input length. This gives the exact-recovery interface needed by discrete local search.
--
--   Differences from the source:
--   - encoding: polynomial-time maps on explicitly supplied rational input → self-delimiting binary codes and the published Cook Turing-machine runtime, with a tagged input/answer pair for decoding; reason: one uniform machine and exponent are chosen before all instances; these codes are polynomially interconvertible with explicit binary lists
--   - encoding: positive dimensions and indices 1 through d → Fin d with d positive and indices 0 through d-1; reason: a bijective relabelling; all real-cube coordinates and all boundary cases are retained
--   - encoding: computational points of a quadratic search problem → rational point vectors supplied as finite strings; analytic KKT itself remains real-valued; reason: a standard Turing input is a finite rational encoding, as in the source proof and its original rounding lemma; no real-oracle algorithm is assumed
--   - generalization: an instance of Quadratic-KKT under the standing assumption |Q_ii| ≤ 1 of §2.1 → every symmetric rational Q, without the diagonal normalization; reason: the source assumes the normalization only after positive rescaling, which preserves exact KKT points and scales ε-KKT tolerances by the same positive factor; restricting to normalized Q recovers the source statement
-- source:
--   Ioannis Anagnostides, Ioannis Panageas, Jingming Yan, STOC 2027 submission #653 (October 2026), p.6 (PDF 7), Lemma 2.2.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding

namespace NetworkEquilibriumCLS.LinearNash

/-- Source and every encoding convention are recorded in the item metadata. -/
theorem quadratic_kkt_rounding :
    ∃ (epsilon : List Bool → ℚ)
      (decode : List (Option (Bool ⊕ Bool)) → List Bool),
    PolyTime (fun x => encRat (epsilon x)) ∧ PolyTime decode ∧
    ∀ (m : ℕ), 0 < m → ∀ p : Quadratic m,
      0 < epsilon (encQuadratic p) ∧
      ∀ y, approxAnswers p (epsilon (encQuadratic p)) y →
        quadraticSearch.answer (encQuadratic p) (decode (pairCode (encQuadratic p) y)) := by sorry

end NetworkEquilibriumCLS.LinearNash
