-- Prove2me | Theorems.Thm_OnlineBeckFiala_eq_10
-- name    : OnlineBeckFiala.eq_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:33:50.060707+00:00
-- url     : https://prove2.me/theorems/b5b21779-33e3-4e93-bb4e-85c6db443e88
-- title:
--   Eq. (10) — the potential has an exponential tail: $P\{u(Y)>r\}\le\frac2Ze^{-r}$
-- statement:
--   Let $u:\mathbb R\to\mathbb R$ be a potential with $e^{-u}$ integrable on $(-1,1)$, let $Z=\int_{-1}^1e^{-u(y)}\,dy$, and let $Y$ have density $Z^{-1}e^{-u}$ on $(-1,1)$. Then for every real $r$,
--   $$P\{u(Y)>r\}=\frac1Z\int_{\{y\in(-1,1):\,u(y)>r\}}e^{-u(y)}\,dy\le\frac2Ze^{-r}.$$
--
--   This is the starting observation of §3.1: the potential itself has an exponential tail, so a potential whose curvature is controlled by $u$ inherits a tail bound for its curvature.
--
--   **Formalization Note** Both the equality and the inequality of the display are stated. The law of $Y$ vanishes off $(-1,1)$.
--
--   Differences from the source:
--   - generalization: the potential u of §3 (eq. (12)) → every u : ℝ → ℝ with e^{−u} integrable on (−1, 1); reason: §3.1 speaks of the potential being constructed, and the bound holds for any such u; the u of (12) is one (0 < e^{−u} ≤ 1 on (−1, 1)), so the statement specializes to the page's
--   - encoding: Y has density Z⁻¹e^{−u} on (−1, 1), u = +∞ off (−1, 1) → u real-valued with e^{−u} integrable on (−1, 1); law potLaw u; reason: integrability is the Lean form of Y having a density; u is never read off (−1, 1)
-- source:
--   Altschuler, Tikhomirov, Online Beck–Fiala Down to Logarithmic Sparsity, arXiv:2607.14238 (held version, sha256 5a1529d2…), p.6, §3.1, eq. (10)

import Mathlib
import Definitions.Def_OnlineBeckFiala_IsBalanced

open MeasureTheory

namespace OnlineBeckFiala

/-- **Eq. (10), §3.1, p.6.** Altschuler, Tikhomirov, *Online Beck–Fiala Down to Logarithmic
Sparsity*, arXiv:2607.14238 (held version, sha256 5a1529d2…): "let Y have density Z⁻¹e^{−u} on
(−1, 1). … P{u(Y) > r} = (1/Z) ∫_{y∈(−1,1): u(y)>r} e^{−u(y)} dy ≤ (2/Z) e^{−r}. (10)"

**Formalization Note.** Stated for every potential `u : ℝ → ℝ` with `e^{−u}` integrable on `(−1, 1)`
(the §3.1 sentence is read for a general `u`; the `u` of (12) is one, since `0 < e^{−u} ≤ 1` there),
and for every real `r`. The law of `Y` is `potLaw u`, which vanishes off `(−1, 1)`. Both relations
of the display are stated: the equality `P{u(Y) > r} = (1/Z) ∫_{y∈(−1,1): u(y)>r} e^{−u(y)} dy`
and the bound by `(2/Z) e^{−r}`. -/
theorem eq_10 (u : ℝ → ℝ) (hu : IntegrableOn (fun y => Real.exp (-u y)) (Set.Ioo (-1) 1))
    (r : ℝ) :
    potLaw u {y | r < u y} =
        ENNReal.ofReal ((Zu u)⁻¹ * ∫ y in {y | y ∈ Set.Ioo (-1 : ℝ) 1 ∧ r < u y}, Real.exp (-u y)) ∧
      potLaw u {y | r < u y} ≤ ENNReal.ofReal (2 / Zu u * Real.exp (-r)) := by sorry

end OnlineBeckFiala
