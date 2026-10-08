-- Prove2me | Theorems.Thm_GoldieRenewal_Implicit_lemma_9_1
-- name    : GoldieRenewal.Implicit.lemma_9_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:10:00.19137+00:00
-- url     : https://prove2.me/theorems/5e243e04-878a-46b6-a802-b40fd179cfb3
-- title:
--   Lemma 9.1 — if f ≥ 0, f ∈ L¹(ℝ) and f(t + ε) ≥ θ(ε)f(t) with θ(ε) → 1, then f is dRi
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ satisfy $f\ge0$ and $f\in L^1(\mathbb R)$, and suppose there is a function $\theta$ with $\theta(\varepsilon)\to1$ as $\varepsilon\downarrow0$ such that
--   $$
--   f(t+\varepsilon)\ge\theta(\varepsilon)\,f(t)\qquad\text{for all }\varepsilon>0,\ t\in\mathbb R .
--   $$
--   Then $f$ is directly Riemann-integrable.
--
--   This criterion is the route by which smoothed functions $\check f$ are shown to be admissible in the key renewal theorem (Lemma 9.2).
--
--   **Formalization Note** The inequality is required at every point; direct Riemann integrability is Feller's definition (see the definition file).
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 143, Lemma 9.1

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_DRi
open MeasureTheory Filter Topology

namespace GoldieRenewal.Implicit

/-- **Lemma 9.1** (Goldie 1991, Ann. Appl. Probab. 1(1), p. 143). If `f ≥ 0`, `f ∈ L¹(ℝ)` and
`f(t + ε) ≥ θ(ε) f(t)` for all `ε > 0` and `t ∈ ℝ`, where `θ(ε) → 1` as `ε ↓ 0`, then `f` is
directly Riemann-integrable (dRi).

**Formalization Note** `f` is a genuine function (the inequality is required at every point, not
almost everywhere); `θ : ℝ → ℝ` is only used at `ε > 0`, and "`θ(ε) → 1` as `ε ↓ 0`" is the limit
along `𝓝[>] 0`. dRi is `IsDRi` (Feller's definition, see its docstring). -/
theorem lemma_9_1 (f : ℝ → ℝ) (hf_nonneg : ∀ t, 0 ≤ f t) (hf_int : Integrable f)
    (θ : ℝ → ℝ) (hθ : Tendsto θ (𝓝[>] 0) (𝓝 1))
    (hshift : ∀ ε : ℝ, 0 < ε → ∀ t : ℝ, θ ε * f t ≤ f (t + ε)) :
    IsDRi f := by sorry

end GoldieRenewal.Implicit
