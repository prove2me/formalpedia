-- Prove2me | Theorems.Thm_GinibrePermanent977_Anticoncentration_Supplement_lemma_C_4
-- name    : GinibrePermanent977.Anticoncentration.Supplement.lemma_C_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:36:09.437113+00:00
-- url     : https://prove2.me/theorems/16318356-a6b2-408a-96d3-93f1e15c0554
-- title:
--   Lemma C.4 — Quaternionic Gaussian left-right symmetry
-- statement:
--   Let $d_1,\ldots,d_p\in\mathbb H$ be fixed. Let $g_1,\ldots,g_p$ and $h_1,\ldots,h_p$ be independent standard quaternionic Gaussians, whose four real coordinates have variance $1/4$. Then the full quaternion-valued laws satisfy
--   $$\sum_{j=1}^p g_jd_j\overset d=\sum_{j=1}^p d_jh_j.$$
--   This symmetry supplies the Gaussian conversion used in the quaternionic suffix contraction. It is equality in distribution, with no pathwise equality or restriction on the fixed coefficients. The empty list gives zero on both sides.
--
--   Differences from the source:
--
--   - encoding: 1-based row and column indices → zero-based Fin indices, with source row k+1 represented by k; reason: finite reindexing preserves all rows and increasing multiplication order
--   - encoding: independent random inputs → coordinate functions under their probability product laws; reason: these are exactly the joint laws of independent Borel random variables; no moment or density restriction is added
--   - encoding: equality in distribution → IdentDistrib of the two quaternion-valued maps on standard Gaussian vector laws; reason: IdentDistrib includes a.e. measurability and equality of full laws
-- source:
--   Frederic Koehler, Pui Kuen Leung, STOC 2027 submission #977 (October 2026), Lemma C.4, p.20 (PDF SHA256 e25737f1d5e3492905f8eeaa41d92c55d95f73622a3b5846cc87aac6a346d4ec)

import Mathlib
import Definitions.Def_GinibrePermanent977_Anticoncentration_Model
open MeasureTheory ProbabilityTheory
open scoped Quaternion BigOperators

namespace GinibrePermanent977.Anticoncentration.Supplement

/-- Lemma C.4, p.20: equality of full quaternion-valued laws, including the empty sum. -/
theorem lemma_C_4 (p : ℕ) (d : Fin p → Scalar.quaternion.K) :
    IdentDistrib (fun g : Fin p → Scalar.quaternion.K => ∑ j, g j * d j)
      (fun h : Fin p → Scalar.quaternion.K => ∑ j, d j * h j)
      (gaussVec .quaternion p) (gaussVec .quaternion p) := by sorry

end GinibrePermanent977.Anticoncentration.Supplement
