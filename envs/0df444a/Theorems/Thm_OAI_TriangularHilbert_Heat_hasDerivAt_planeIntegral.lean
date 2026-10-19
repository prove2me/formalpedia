-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_hasDerivAt_planeIntegral
-- name    : OAI.TriangularHilbert.Heat.hasDerivAt_planeIntegral
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:51:56.997985+00:00
-- url     : https://prove2.me/theorems/8252b56d-0395-43b2-8391-9a3efab1854b
-- title:
--   Differentiating plane integrals in the centre sum
-- statement:
--   Centres with $p_0+p_1+p_2=d$ are parametrized by $\mathrm{chart}(i,d,z)$, $z\in\mathbb R^2$, and $\mathrm{planeIntegral}(f,d)=\int_{\mathbb R^2}f(\mathrm{chart}(2,d,z))\,dz$. Let $f,g:\mathbb R^3\to\mathbb R$ be measurable and suppose that $g$ is the derivative of $f$ in its $i$-th coordinate:
--   $$
--   \frac{\partial}{\partial p_i}f(p)=g(p)\quad\text{for all }p .
--   $$
--   Suppose $|f(\mathrm{chart}(i,d,z))|\le B(z)$ and $|g(\mathrm{chart}(i,e,z))|\le B(z)$ for $e\in(d-1,d+1)$, with $B$ integrable. Then $d\mapsto\mathrm{planeIntegral}(f,d)$ is differentiable with derivative $\mathrm{planeIntegral}(g,d)$.
--
--   Changing the centre sum is the same as moving one centre.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/PlaneIntegral.lean#L35-L52

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
universe uι
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

theorem OAI.TriangularHilbert.Heat.hasDerivAt_planeIntegral {f g : (Three → ℝ) → ℝ} {B : (ℝ × ℝ) → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hB : Integrable B)
    (i : Three) (d : ℝ)
    (hb0 : ∀ z, ‖f (chart i d z)‖ ≤ B z)
    (hb : ∀ e ∈ Set.Ioo (d-1) (d+1), ∀ z, ‖g (chart i e z)‖ ≤ B z)
    (hd : ∀ p, HasDerivAt (fun t => f (Function.update p i t)) (g p) (p i)) :
    HasDerivAt (planeIntegral f) (planeIntegral g d) d := by sorry
