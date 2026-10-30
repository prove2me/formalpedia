-- Prove2me | Theorems.Thm_FuchsVdGraaf_proposition_2
-- name    : FuchsVdGraaf.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:15:28.162737+00:00
-- url     : https://prove2.me/theorems/f822384b-828d-428a-8fe4-1be61ec38221
-- title:
--   Proposition 2 — $\mathrm{PE}(p_0,p_1) = \tfrac12 - \tfrac12 K(p_0,p_1)$
-- statement:
--   Let $p_0, p_1$ be probability distributions on a finite set $\mathcal X$. Then the probability of error and the Kolmogorov distance determine each other:
--
--   $$
--   \mathrm{PE}(p_0,p_1) = \frac12 - \frac12 K(p_0,p_1).
--   $$
--
--   This identity is what makes the quantum $\mathrm{PE}$ and $K$ optimised by the same measurement, and it converts Helstrom's formula for $\mathrm{PE}(\rho_0,\rho_1)$ into the trace-distance formula for $K(\rho_0,\rho_1)$.
--
--   Differences from the source: none.
-- source:
--   Fuchs and van de Graaf, Cryptographic Distinguishability Measures for Quantum Mechanical States, arXiv:quant-ph/9712042v2, Proposition 2, eq. (19), p.12

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsProbDist
import Definitions.Def_FuchsVdGraaf_errorProb
import Definitions.Def_FuchsVdGraaf_kolmogorov

namespace FuchsVdGraaf

/-- Fuchs and van de Graaf, arXiv:quant-ph/9712042v2, Proposition 2, eq. (19), p.12 (restated
as (42), p.17): for probability distributions `p₀`, `p₁` on a finite set,
`PE(p₀, p₁) = ½ − ½ K(p₀, p₁)`.

**Formalization Note.** The standing hypothesis of §2 (p.4), that `p₀` and `p₁` are probability
distributions on a finite set, is stated as `IsProbDist`. -/
theorem proposition_2 {X : Type} [Fintype X] (p0 p1 : X → ℝ)
    (hp0 : IsProbDist p0) (hp1 : IsProbDist p1) :
    errorProb p0 p1 = 1 / 2 - 1 / 2 * kolmogorov p0 p1 := by sorry

end FuchsVdGraaf
