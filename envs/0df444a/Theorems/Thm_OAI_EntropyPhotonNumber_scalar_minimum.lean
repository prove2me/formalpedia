-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_scalar_minimum
-- name    : OAI.EntropyPhotonNumber.scalar_minimum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:21:48.471212+00:00
-- url     : https://prove2.me/theorems/4d5b8018-bf45-456d-8fa0-ed7c2a672a17
-- title:
--   Closed form $f(x)f(y)/f(x+y)$ for the minimum of the scalar interpolation quadratic
-- statement:
--   Let $f:\mathbb{R}\to\mathbb{R}$ be $f(x)=\dfrac{x}{\sinh x}$ for $x\ne0$, with $f(0)=1$, and let $b(x)=f(x)\cosh x$ (so $b(x)=x\coth x$ for $x\neq0$ and $b(0)=1$). For a function $D$ put
--   $$
--   \mathcal E_D(s,t)=\Bigl(\int_0^1D\bigl((1-\theta)s+\theta t\bigr)\,d\theta\Bigr)^{-1}.
--   $$
--
--   **Theorem.** Let $B_0,D:\mathbb{R}\to\mathbb{R}$ satisfy:
--   - $D$ is continuous on $(0,\infty)$ and $D(q)>0$ for $q>0$;
--   - $B_0$ is differentiable at every $q>0$ with $B_0'(q)=-D(q)/2$;
--   - $B_0\bigl(f(x)^2\bigr)=b(x)$ for every real $x$.
--
--   Then for all real $x,y$, with $E=\mathcal E_D\bigl(f(x)^2,f(y)^2\bigr)$,
--   $$
--   \frac12\Bigl(b(x)+b(y)-\frac{(x-y)^2}{b(x)+b(y)+2E}\Bigr)=\frac{f(x)\,f(y)}{f(x+y)} .
--   $$
--
--   For $m>0$ and $\xi\ne0$, $m$ times the left side is the minimum over $\varphi\in\mathbb{C}$ of $Q(\xi,\varphi)/|\xi|^2$. Here $Q$ is the five-term quadratic form built from the four weights $mf(x)e^{\pm x}$, $mf(y)e^{\pm y}$ (each with factor $\tfrac14$) and the extra weight $mE$. The theorem identifies this minimum in closed form, which is the scalar core of the four-weight interpolation inequality.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Interpolation.lean#L501-L536

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy
import Definitions.Def_OAI_InformationTheory_PhotonNumber_GibbsVariational
import Definitions.Def_OAI_Analysis_Herglotz
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Interpolation

open OAI OAI.EntropyPhotonNumber
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open DiagonalForms.System MeasureTheory Set Filter Topology

theorem OAI.EntropyPhotonNumber.scalar_minimum {B₀ D : ℝ → ℝ}
    (hc : ContinuousOn D (Ioi 0)) (hp : ∀ q, 0 < q → 0 < D q)
    (hd : ∀ q, 0 < q → HasDerivAt B₀ (-D q/2) q)
    (hb : ∀ x, B₀ (f x^2) = b x) (x y : ℝ) :
    (b x+b y-(x-y)^2/(b x+b y+2*genericAdditionalE D (f x^2) (f y^2)))/2 =
      f x*f y/f (x+y) := by sorry
