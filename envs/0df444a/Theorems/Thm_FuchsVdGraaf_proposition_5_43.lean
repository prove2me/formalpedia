-- Prove2me | Theorems.Thm_FuchsVdGraaf_proposition_5_43
-- name    : FuchsVdGraaf.proposition_5_43
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:15:36.676923+00:00
-- url     : https://prove2.me/theorems/720318d3-9271-4ee9-a446-4d8de0dc0f11
-- title:
--   Proposition 5, eq. (43) — $1 - B \le K \le \sqrt{1-B^2}$ (classical)
-- statement:
--   Let $p_0, p_1$ be probability distributions on a finite set, with Bhattacharyya coefficient $B(p_0,p_1)$ and Kolmogorov distance $K(p_0,p_1)$. Then
--
--   $$
--   1 - B(p_0,p_1) \;\le\; K(p_0,p_1) \;\le\; \sqrt{1 - B(p_0,p_1)^2} .
--   $$
--
--   This is the first of the three relations of Proposition 5. Its quantum version, with $K(\rho_0,\rho_1) = \tfrac12\mathrm{Tr}|\rho_0-\rho_1|$, is the trace-distance/fidelity inequality (46).
--
--   Differences from the source: none.
-- source:
--   Fuchs and van de Graaf, Cryptographic Distinguishability Measures for Quantum Mechanical States, arXiv:quant-ph/9712042v2, Proposition 5, eq. (43), p.17

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsProbDist
import Definitions.Def_FuchsVdGraaf_kolmogorov
import Definitions.Def_FuchsVdGraaf_bhattacharyya

namespace FuchsVdGraaf

/-- Fuchs and van de Graaf, arXiv:quant-ph/9712042v2, Proposition 5, eq. (43), p.17: for
probability distributions `p₀`, `p₁` on a finite set,
`1 − B(p₀, p₁) ≤ K(p₀, p₁) ≤ √(1 − B(p₀, p₁)²)`. -/
theorem proposition_5_43 {X : Type} [Fintype X] (p0 p1 : X → ℝ)
    (hp0 : IsProbDist p0) (hp1 : IsProbDist p1) :
    1 - bhattacharyya p0 p1 ≤ kolmogorov p0 p1 ∧
      kolmogorov p0 p1 ≤ Real.sqrt (1 - bhattacharyya p0 p1 ^ 2) := by sorry

end FuchsVdGraaf
