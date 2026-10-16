-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_logarithmicMean_exp_pair
-- name    : OAI.EntropyPhotonNumber.logarithmicMean_exp_pair
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:20:11.859609+00:00
-- url     : https://prove2.me/theorems/0487139c-2416-433a-b885-e5e7e44d7ac7
-- title:
--   The logarithmic mean of $m f(x)e^{x}$ and $m f(x)e^{-x}$ equals $m$
-- statement:
--   Let $f:\mathbb{R}\to\mathbb{R}$ be $f(x)=\dfrac{x}{\sinh x}$ for $x\ne0$, with $f(0)=1$, and let $b(x)=f(x)\cosh x$ (so $b(x)=x\coth x$ for $x\neq0$ and $b(0)=1$). For real $X,Y$, the logarithmic mean is
--   $$
--   L(X,Y)=\begin{cases}X,&X=Y,\\\dfrac{Y-X}{\log Y-\log X},&X\ne Y.\end{cases}
--   $$
--
--   **Theorem.** For every $m>0$ and every real $x$,
--   $$
--   L\bigl(m\,f(x)\,e^{x},\ m\,f(x)\,e^{-x}\bigr)=m .
--   $$
--
--   The factor $f(x)=x/\sinh x$ is exactly the normalization that makes the logarithmic mean of $e^{x}$ and $e^{-x}$ equal to $1$. In the interpolation argument, a comparison inequality that holds for the two weights $mf(x)e^{\pm x}$ is transferred to their logarithmic mean, and this identity shows that the resulting weight is simply $m$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Interpolation.lean#L350-L369

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

theorem OAI.EntropyPhotonNumber.logarithmicMean_exp_pair {m : ℝ} (hm : 0 < m) (x : ℝ) :
    logMean (m*f x*Real.exp x) (m*f x*Real.exp (-x)) = m := by sorry
