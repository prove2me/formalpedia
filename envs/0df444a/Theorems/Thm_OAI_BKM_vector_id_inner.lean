-- Prove2me | Theorems.Thm_OAI_BKM_vector_id_inner
-- name    : OAI.BKM.vector_id_inner
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:40:08.817458+00:00
-- url     : https://prove2.me/theorems/fab73eae-3a73-4bf6-acfd-539f0f73965f
-- title:
--   Pairing with the identity in the logarithmic-mean coordinates gives the weighted mean
-- statement:
--   Let $E$ be a complex Hilbert space with a Hilbert basis $(b_j)_{j\in J}$, and let $p:J\to(0,\infty)$ be summable. Let $L(x,y)$ denote the logarithmic mean ($L(x,y)=\frac{y-x}{\log y-\log x}$ for $x\neq y$, $L(x,x)=x$). For a bounded operator $Z$ on $E$ let $\mathrm v(Z)\in\ell^2(J\times J)$ be its logarithmic-mean coordinate vector
--   $$\mathrm v(Z)_{ij}=\sqrt{L(p_i,p_j)}\;\langle b_i,Zb_j\rangle\qquad(i,j\in J),$$
--   which is square summable. Then
--   $$\bigl\langle\mathrm v(\mathrm{Id}),\,\mathrm v(Z)\bigr\rangle_{\ell^2(J\times J)}=\sum_{j\in J}p_j\,\langle b_j,Zb_j\rangle .$$
--
--   Thus $\|\mathrm v(Z)\|^2=\sum_{i,j}L(p_i,p_j)|\langle b_i,Zb_j\rangle|^2$ is the Bogoliubov–Kubo–Mori quadratic form of $Z$ relative to $\rho=\sum_jp_j|b_j\rangle\langle b_j|$, and the identity says that the component of $\mathrm v(Z)$ along $\mathrm v(\mathrm{Id})$ is the mean $\operatorname{Tr}\rho Z$. This is the basic step for decomposing the BKM form into a variance plus the squared mean.
--
--   **Formalization Note** The right side is the `tsum` `BKM.mean b p Z`; the inner product on $\ell^2$ is conjugate-linear in the first argument.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/FiniteVariation.lean#L2526-L2544

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
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Contraction
import Definitions.Def_OAI_InformationTheory_PhotonNumber_FiniteVariation

open OAI OAI.BKM
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open Module
open scoped ComplexConjugate BigOperators Matrix
open NormedSpace
open scoped Matrix.Norms.Operator
open scoped Topology
open MeasureTheory NormedSpace
open Filter Asymptotics Topology
open ContinuousLinearMap
open scoped BigOperators ComplexConjugate
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem OAI.BKM.vector_id_inner (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 < p j) (hs : Summable p)
    (Z : E →L[ℂ] E) :
    inner ℂ (vector b p hp hs (ContinuousLinearMap.id ℂ E)) (vector b p hp hs Z)=mean b p Z := by sorry
