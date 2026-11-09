-- Prove2me | Theorems.Thm_MinimaxAltRegret_Main_proposition_C_1
-- name    : MinimaxAltRegret.Main.proposition_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:54.173195+00:00
-- url     : https://prove2.me/theorems/4a41b769-1cd9-49aa-9ecb-8161c8f33a42
-- title:
--   Proposition C.1 — density feasibility and strict correction bounds
-- statement:
--   For a positive dimension d, positive horizon T, full-dimensional compact convex body X, and arbitrary convex losses f_t:X to [-1,1], form Algorithm 2's density at eta=1/10. For every round through the terminal action,
--
--   $$p_t\in\Delta_X,\qquad 0<\Gamma_t(x)<2\quad(x\in X),$$
--
--   where Gamma_t(x)=1-4 eta (f_(t-1)(x)-m)-2 eta^2((f_(t-1)(x)-m)^2-H), with m and H taken under q_(t-1). Membership in Delta_X means integrability, pointwise nonnegativity and total integral one. The vector function x p_t(x) is integrable as well, making the exact Option I mean a genuine Bochner integral.
--
--   This certifies the entire corrected density and both strict inequalities without adding boundary continuity or assuming normalization.
--
--   Differences from the source:
--   - encoding: rounds 1 through T and the terminal action x_(T+1) → zero-based losses and actions, with action T terminal and source score R_t stored at index t; reason: a bijective reindexing preserves every summand and includes the same terminal update
--   - encoding: a d-dimensional compact convex set X and convex functions defined on X → a compact convex subset of EuclideanSpace R (Fin d) with nonempty interior, and ambient functions restricted by ConvexOn and pointwise bounds on X; reason: nonempty interior is exactly full affine dimension; arbitrary extensions outside X change no source instance, and no continuity is required on the boundary
--   - encoding: a density p_t and the exact mean used by Algorithm 2 → density membership explicitly includes Integrable, and the vector mean integrand is also asserted Integrable; reason: the source integrals are genuine integrals; bounded convex losses are a.e. continuous on a finite-volume compact body, and this records their definedness without restricting boundary values
-- source:
--   Mengxiao Zhang, STOC 2027 submission #57 (October 2026), printed p. 22 / PDF p. 23, Proposition C.1; SHA-256 6db5a23e9e92d250b4dea7995bf34c9930d39a95df90f5d3fdc715ca26044f31

import Mathlib
import Definitions.Def_MinimaxAltRegret_Main_Sampling
import Definitions.Def_MinimaxAltRegret_Main_LowerConstruction

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace MinimaxAltRegret.Main

theorem proposition_C_1 (d T : ℕ) (hd : 0 < d) (hT : 0 < T)
    (X : Set (Point d)) (hX : convexBody X) (f : ℕ → Point d → ℝ)
    (hf : convexLosses X T f) :
    ∀ t ≤ T, bodyDensity X (continuousDensity X T f t) ∧
      (∀ x ∈ X, 0 < continuousGamma X (1/10) (continuousScore T f t)
        (continuousPrevious T f t) x ∧
        continuousGamma X (1/10) (continuousScore T f t) (continuousPrevious T f t) x < 2) ∧
      Integrable (fun x => continuousDensity X T f t x • x) (bodyMeasure X) := by sorry

end MinimaxAltRegret.Main
