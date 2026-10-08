-- Prove2me | Theorems.Thm_GlynnSTS_NoAttain_C0_subset_D
-- name    : GlynnSTS.NoAttain.C0_subset_D
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:09:56.63958+00:00
-- url     : https://prove2.me/theorems/17b050b2-f5fb-4250-96c1-460fdf4b57ab
-- title:
--   Proof of Proposition 4.26, p. 14 — (2.3i) and (4.25) force g to be discontinuous on all of C₀[0,1]
-- statement:
--   Let $B$ be a standard Brownian motion on $[0,1]$, regarded as a random element of $C[0,1]$. Let $g: C[0,1]\to\mathbb R$ be positively homogeneous, $g(ax)=a\,g(x)$ for $a>0$ (condition (2.3i)), and suppose that for some $\sigma>0$ and $\alpha>0$
--   $$P\{g(\sigma B)=\alpha\sigma\}=1 \qquad (4.25).$$
--   Then $g$ is discontinuous at every point of $C_0[0,1]=\{x\in C[0,1]: x(0)=0\}$:
--   $$C_0[0,1]\subseteq D(g).$$
--
--   Since $B\in C_0[0,1]$ almost surely, this gives $P\{B\in D(g)\}=1$, contradicting (2.3iv); this is the "something stronger" announced at the start of the proof of Proposition 4.26.
--
--   **Formalization Note** The paper concludes "$D(g)=C_0[0,1]$", but its argument proves only the inclusion $C_0[0,1]\subseteq D(g)$ ($D(g)$ may also contain paths with $x(0)\ne0$); the inclusion is what is stated, and it suffices for the contradiction. Only (2.3i) is assumed; the remaining conditions of $\mathcal M$ are not needed, which makes the statement stronger.
-- source:
--   Glynn & Iglehart, Simulation output analysis using standardized time series, Math. Oper. Res. 15 (1990), p. 14, proof of Proposition 4.26 ("D(g) = C₀[0, 1]")

import Mathlib
import Definitions.Def_GlynnSTS_NoAttain_Setting

namespace GlynnSTS.NoAttain

open MeasureTheory ProbabilityTheory

/-- The conclusion of the proof of Proposition 4.26, p. 14, in the form the argument proves:
if `g` satisfies (2.3i) and (4.25) `P{g(σB) = ασ} = 1` for some `σ > 0` and `α > 0`, then `g`
is discontinuous at every point of `C₀[0,1]`. -/
theorem C0_subset_D {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : Ω → C(unitInterval, ℝ)) (hB : GlynnSTS.Limit.IsStdBMC P B)
    (g : C(unitInterval, ℝ) → ℝ)
    (hhom : ∀ a : ℝ, 0 < a → ∀ x, g (a • x) = a * g x)
    (σ α : ℝ) (hσ : 0 < σ) (hα : 0 < α)
    (h425 : ∀ᵐ ω ∂P, g (σ • B ω) = α * σ) :
    C0 ⊆ GlynnSTS.Limit.D g := by sorry

end GlynnSTS.NoAttain
