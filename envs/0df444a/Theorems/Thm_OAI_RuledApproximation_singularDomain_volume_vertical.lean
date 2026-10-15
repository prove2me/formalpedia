-- Prove2me | Theorems.Thm_OAI_RuledApproximation_singularDomain_volume_vertical
-- name    : OAI.RuledApproximation.singularDomain_volume_vertical
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:21:37.59943+00:00
-- url     : https://prove2.me/theorems/54b45a17-f3a6-4a2f-923f-954104f8020c
-- title:
--   Area of the singular base domain by vertical slices
-- statement:
--   For real numbers $p,\gamma,c$ let $\Delta_p(b)=b^2\big(\tfrac p4+(2-p)b^2\big)$, let $\varphi_c(b)=\tfrac12+c^2\Delta_p(b)+c^{5/2}$ be the ceiling function, and let
--
--   $$
--   \Omega_{p,\gamma,c}=\big\{(b_0,b_1)\in\mathbb{R}^2:\ c^\gamma\le b_1\le2,\ |b_0|\le b_1,\ b_1\le\varphi_c(b_0)\big\}.
--   $$
--
--   Assume that $\varphi_c(b)\le2$ for every $b$ with $|b|\le2$. Then the Lebesgue area of $\Omega_{p,\gamma,c}$ is
--
--   $$
--   |\Omega_{p,\gamma,c}|=\int_{-2}^{2}\max\Big(\varphi_c(b)-\max\big(c^\gamma,|b|\big),\,0\Big)\,db .
--   $$
--
--   Above the abscissa $b$, the domain occupies the vertical segment from $\max(c^\gamma,|b|)$ up to the ceiling $\varphi_c(b)$. This formula is the first step in the asymptotic expansion of the area of the base domain of the singular covering of the regular tetrahedron as $c\to0^+$: combined with the analogous formula for the band $\{c^\gamma\le b_1\le\tfrac12,\ |b_0|\le b_1\}$ it reduces the area difference to a one-dimensional integral. The cap hypothesis holds for all sufficiently small $c>0$.
--
--   **Formalization Note** The left side is `volume.real (singularDomain p gamma c)` and $\Delta_p$ is `ceilingPolynomial p`. The powers $c^\gamma$ and $c^{5/2}$ are real powers (`Real.rpow`); no sign conditions on $p,\gamma,c$ are imposed. The cap hypothesis makes the constraint $b_1\le2$ in the definition of the domain redundant.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/ConeVolume.lean#L101-L115

import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice
import Definitions.Def_OAI_Geometry_RuledCovering_Nilpotent
import Definitions.Def_OAI_Geometry_RuledCovering_SingularField
import Definitions.Def_OAI_Geometry_RuledCovering_PlanarIntegration
import Definitions.Def_OAI_Geometry_RuledCovering_ConeVolume

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.singularDomain_volume_vertical (p gamma c : ℝ)
    (hcap : ∀ b : ℝ, |b| ≤ 2 → (1/2:ℝ)+c^2*ceilingPolynomial p b+c^(5/2:ℝ) ≤ 2) :
    volume.real (singularDomain p gamma c) = ∫ b in Icc (-2:ℝ) 2,
      max ((1/2:ℝ)+c^2*ceilingPolynomial p b+c^(5/2:ℝ)-max (c^gamma) |b|) 0 := by sorry
