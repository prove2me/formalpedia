-- Prove2me | Theorems.Thm_MonoABPWidth_Hierarchy_Supplement_theorem_6_4
-- name    : MonoABPWidth.Hierarchy.Supplement.theorem_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:37:26.795528+00:00
-- url     : https://prove2.me/theorems/cb51df41-950c-4561-8911-a8099a451ea7
-- title:
--   Theorem 6.4 — one family beyond slowly growing widths
-- statement:
--   There exists one real p-family $f$ computable by monotone formulas of polynomial total gate count such that, for every natural-valued width function $W$ satisfying the following little-o condition,
--   $$W(t)=o\left(\frac{\log_2 t}{(\log_2\log_2 t)^2}\right),\qquad f\notin\mathrm{mVBP}_{W(t)}.$$
--   The quantifier order is $\exists f\,\forall W$. No monotonicity, divergence, or eventual lower bound on $W$ is assumed. Formula depth is unrestricted. This places a single formula family beyond every width class in the specified regime.
--
--   Differences from the source:
--   - encoding: one p-family outside all widths in the stated little-o class → one PolynomialFamily followed by every natural-valued W with IsLittleO atTop; reason: the order of quantifiers and the squared base-two iterated-log denominator are preserved; finite initial values do not affect little-o
-- source:
--   Julian Dörfler, Alexander Rogovskyy, STOC 2027 submission #927 (October 2026), Theorem 6.4, p.16, PDF17

import Definitions.Def_MonoABPWidth_Hierarchy_Supplement_families

open scoped BigOperators ENNReal

namespace MonoABPWidth.Hierarchy.Supplement

/-- Theorem 6.4, p.16 (PDF17): one family works for every little-o width
function. No monotonicity or eventual positive lower bound is imposed on W. -/
theorem theorem_6_4 : ∃ f : PolynomialFamily, InMVF f ∧
    ∀ W : ℕ → ℕ,
      Asymptotics.IsLittleO Filter.atTop (fun t => (W t : ℝ)) widthThreshold →
      ¬ InMVBP W f := by sorry

end MonoABPWidth.Hierarchy.Supplement
