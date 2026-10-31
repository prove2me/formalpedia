-- Prove2me | Theorems.Thm_MinBuying_lemmaEC2_continuous_smoothing
-- name    : MinBuying.lemmaEC2_continuous_smoothing
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T16:26:55.007754+00:00
-- url     : https://prove2.me/theorems/3d094afb-c9b0-4367-b038-4b7c07eebf5b
-- title:
--   Lemma EC.2: continuous regular approximation
-- statement:
--   For a positive finite triangular instance whose optimal uniform revenue is at most one, there exists a positive smallness threshold such that every sufficiently small $0<\delta<1$ admits an independent continuous regular instance with the same revenue at the original cap-price vector and optimal uniform revenue at most $1/(1-\delta)$.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, 47 PDF pages (main pp.1–27; companion ec1–ec20). https://doi.org/10.2139/ssrn.5178133 . PDF pp.45–47/ec18–ec20, Lemma EC.2.

import Definitions.Def_MinBuying_Triangular
import Definitions.Def_MinBuying_Regularity

open MeasureTheory

namespace MinBuying

/-- Lemma EC.2, PDF pp.45--47: for every sufficiently small positive
smoothing width, cap-pricing revenue is preserved exactly while the
optimal uniform revenue increases by at most the displayed factor. -/
theorem lemmaEC2_continuous_smoothing (n : ℕ) (hn : 0 < n)
    (I : TriangularInstance n) (hUP : UPRevenue (triangularJoint I) ≤ 1) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < min 1 δ₀ →
      ∃ F : Fin n → Measure ℝ,
        RegularInstance F ∧
        Revenue (productLaw F) I.cap = Revenue (triangularJoint I) I.cap ∧
        UPRevenue (productLaw F) ≤ 1 / (1 - δ) := by
  sorry

end MinBuying
