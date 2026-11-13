-- Prove2me | Theorems.Thm_LocalLemmaHierarchy_Completeness_theorem_3_9
-- name    : LocalLemmaHierarchy.Completeness.theorem_3_9
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T00:20:12.401892+00:00
-- url     : https://prove2.me/theorems/a90e6bd6-6da6-45eb-8f4e-9f4a098e88f6
-- title:
--   Theorem 3.9 — quadratic completeness: $0\le R-R_q\le d_q/c_*\le\pi^2/(c_*(q+1)^2)$
-- statement:
--   Let $\mathcal R$ represent a nonconstant family $Z$ and $q\ge1$; put $d_q=2(1-\cos(\pi/(q+1)))$. Then
--   $$0\le R-R_q\le\frac{d_q}{c_*}\le\frac{\pi^2}{c_*(q+1)^2},\qquad(3.9)$$
--   $$0\le1-\frac{R_q}{R}\le\frac{\pi^2}{c_*R(q+1)^2}.\qquad(3.10)$$
--   The same bounds hold for every finite grouped presentation (with $R_q$ replaced by the radius it certifies).
--
--   Differences from the source:
--   - generalization: the sites form a countable set V → V is any type (no countability assumption); reason: no step of the proofs uses countability; the statement for countable V is the special case
--   - encoding: a total order ≺_{v,a} on D_{v,a} \ {v} → a rank R.rank v a : V → ℕ injective on D_{v,a} \ {v}, with w ≺ u ↔ rank w < rank u; reason: every total order on a finite set is induced by such a rank, and only comparisons are used
--   - encoding: a polynomial family Z = (Z_U)_{U ⋐ V} in the variables z_τ → Z : Finset V → MvPolynomial T ℝ, evaluated at complex z by MvPolynomial.aeval; reason: Z_∅ = 1 and the deletion identity with real c_{v,a} > 0 determine every Z_U recursively, so its coefficients are real; the source families are exactly these
--   - encoding: radii R_U, R, R_q in [0, +∞] (sup over t ≥ 0, inf over regions, empty infimum +∞) → ℝ≥0∞-valued ⨆ over t : ℝ≥0 and ⨅ over Finset V; reason: +∞ must be representable (constant families); ℝ≥0∞ suprema and infima are the extended-real ones
--   - encoding: 0 ≤ R − R_q ≤ d_q/c_∗ → R_q ≤ R ∧ R ≤ R_q + ENNReal.ofReal (d_q/c_∗) in ℝ≥0∞; reason: avoids truncated subtraction; equivalent for finite R
--   - encoding: (3.10) 0 ≤ 1 − R_q/R ≤ π²/(c_∗ R (q+1)²) → under 0 < R: R_q/R ≤ 1 ∧ 1 − R_q/R ≤ ENNReal.ofReal (π²/(c_∗(q+1)²)) / R; reason: the relative error is undefined at R = 0 (Corollary 3.8 states it for R > 0); the hypothesis only excludes that case
--   - encoding: "the same bounds hold for every finite grouped presentation" → the same bounds for P.radius of every GroupedPresentation R q 1 (rows built at unit moduli, coefficients scaled by t); reason: at uniform moduli the grouping condition does not depend on t > 0 (§3.1), so one presentation at t = 1 serves every t
-- source:
--   Achlioptas, Kritharidis and Zampetakis, A Complete Hierarchy of Local Lemmas, STOC 2027 submission (manuscript sha256 bc1388b0…a434b961), Theorem 3.9, printed p. 10 (PDF p. 12); proof App. F.2, printed pp. 39–40 (PDF pp. 41–42)

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Representation
import Definitions.Def_LocalLemmaHierarchy_Completeness_Histories
import Definitions.Def_LocalLemmaHierarchy_Completeness_Memory
import Definitions.Def_LocalLemmaHierarchy_Completeness_Weights

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness

/-- **Theorem 3.9 (Quadratic completeness)**, printed p. 10 / PDF 12 (proof App. F.2, printed
39–40 / PDF 41–42). For a nonconstant family and `q ≥ 1`, with `d_q = 2(1 − cos(π/(q+1)))`:
`0 ≤ R − R_q ≤ d_q/c_∗ ≤ π²/(c_∗(q+1)²)` (3.9) and `0 ≤ 1 − R_q/R ≤ π²/(c_∗ R (q+1)²)` (3.10); the
same bounds hold for every finite grouped presentation (built at unit moduli; its radius is the
supremum of the uniform moduli it certifies). -/
theorem theorem_3_9 {V T : Type} (R : PosLocalDeletionRep V T)
    (Z : Finset V → MvPolynomial T ℝ) (hRZ : IsRepresentationOf R Z) (hnc : IsNonconstant Z)
    (q : ℕ) (hq : 1 ≤ q) :
    dq q / R.cstar ≤ Real.pi ^ 2 / (R.cstar * ((q : ℝ) + 1) ^ 2) ∧
    (memRadius R q ≤ uniformRadius Z ∧
      uniformRadius Z ≤ memRadius R q + ENNReal.ofReal (dq q / R.cstar)) ∧
    (0 < uniformRadius Z →
      memRadius R q / uniformRadius Z ≤ 1 ∧
      1 - memRadius R q / uniformRadius Z ≤
        ENNReal.ofReal (Real.pi ^ 2 / (R.cstar * ((q : ℝ) + 1) ^ 2)) / uniformRadius Z) ∧
    ∀ P : GroupedPresentation R q (fun _ => 1),
      (P.radius ≤ uniformRadius Z ∧
        uniformRadius Z ≤ P.radius + ENNReal.ofReal (dq q / R.cstar)) ∧
      (0 < uniformRadius Z →
        P.radius / uniformRadius Z ≤ 1 ∧
        1 - P.radius / uniformRadius Z ≤
          ENNReal.ofReal (Real.pi ^ 2 / (R.cstar * ((q : ℝ) + 1) ^ 2)) / uniformRadius Z) := by sorry

end LocalLemmaHierarchy.Completeness
