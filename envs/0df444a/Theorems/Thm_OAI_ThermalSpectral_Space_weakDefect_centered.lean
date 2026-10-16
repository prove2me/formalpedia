-- Prove2me | Theorems.Thm_OAI_ThermalSpectral_Space_weakDefect_centered
-- name    : OAI.ThermalSpectral.Space.weakDefect_centered
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:25:17.277321+00:00
-- url     : https://prove2.me/theorems/51128ed4-0403-4461-b5b4-fad8e276c5a1
-- title:
--   With the mean subtracted, the weak thermal-balance defect equals its centered form
-- statement:
--   Work on the $n$-mode Fock space $F=\ell^2(\mathbb{N}^n,\mathbb{C})$ with number basis $(|k\rangle)_{k\in\mathbb{N}^n}$, annihilation operators $a_1,\dots,a_n$, and the diagonal weight $\hat N=1+\sum_j a_j^\dagger a_j$ (so $\hat N|k\rangle=(1+k_1+\dots+k_n)|k\rangle$). Let $\rho$ be a state (a positive trace-one operator on $F$).
--
--   *Weighted columns.* A weighted column family of $\rho$ is a family $(x_l)_{l\in I}$ in $F$ with $\sum_l\|x_l\|^2<\infty$ such that the vectors $y_l=\hat N^{-3}x_l$ satisfy $\sum_l\|y_l\|^2=1$ and $\sum_l|y_l\rangle\langle y_l|=\rho$. For a bounded operator $Z$, a mode $j$ and $r>0$ put
--   $$\mathbb E(Z)=\sum_l\langle y_l,Zy_l\rangle,\qquad W_j(Z)=(r+1)\sum_l\langle a_jy_l,\,Zy_l\rangle-r\sum_l\langle y_l,\,Z\,a_j^\dagger y_l\rangle$$
--   (well defined since $a_j\hat N^{-3}$ and $a_j^\dagger\hat N^{-3}$ are bounded), the centered weak functional $W^{c}_j(Z)=W_j(Z)-W_j(\mathrm{Id})\,\mathbb E(Z)$, and for $\mu\in\mathbb{C}$ the weak defect
--   $$\Delta_{j,\mu}(Z)=(r+1)\sum_l\bigl\langle (a_j-\mu)y_l,\,Zy_l\bigr\rangle-r\sum_l\bigl\langle y_l,\,Z\,(a_j^\dagger-\bar\mu)y_l\bigr\rangle .$$
--
--   *Spectral data.* Let $(b_l)_{l\in I}$ be a Hilbert basis of $F$, $p_l>0$ with $\sum_lp_l=1$, $r>0$, $h(r)=\log(r+1)-\log r$, $\nu_{lm}=(\log p_l-\log p_m)/h(r)$ and $d_{lm}=(r+1)p_m-rp_l$. Assume the weighted columns are spectral in this basis: $y_l=\sqrt{p_l}\,b_l$ for all $l$. Put
--   $$c_{lm}=\bigl\langle b_l,(a_j-\mu)\,b_m\bigr\rangle=\frac{\langle b_l,a_jy_m\rangle}{\sqrt{p_m}}-\mu\,\delta_{lm}.$$
--
--   **Theorem.** Assume $\sum_{l,m}(1-\nu_{lm})\,d_{lm}\,|c_{lm}|^2<\infty$ and that $\mu$ is the mean of $a_j$ in the sense that
--   $$\sum_{l}p_l\,c_{ll}=0 \quad(\text{a convergent series}).$$
--   Then for every bounded operator $Z$ on $F$
--   $$\Delta_{j,\mu}(Z)=W^{c}_j(Z)=W_j(Z)-W_j(\mathrm{Id})\,\mathbb E(Z).$$
--
--   The defect $\Delta_{j,\mu}$ measures the creation–annihilation balance $(r+1)a_j$ versus $r\,a_j^\dagger$ that characterizes a thermal state of mean photon number $r$ in mode $j$; the result identifies the defect with $\mu$ equal to the mean of $a_j$ with the centered functional, which is the form that the metric estimates control.
--
--   **Formalization Note** The weighted column family is the structure `WeightedColumns ρ`; since its index type is a field of that structure, the statement assumes `X.Index = S.I` and relates the two vector families by `HEq`. The operators $a_j\hat N^{-3}$, $a_j^\dagger\hat N^{-3}$ are `sandwich 0 3` and `creationSandwich 0 3`, and pairings are `CrossEnsemble.pairing`, i.e. series $\sum_l\langle v_l,Zu_l\rangle$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/SpectralForms.lean#L984-L1009

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

open OAI OAI.ThermalSpectral OAI.ThermalSpectral.Space
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
open EntropyPhotonNumber Annihilation WeightedGenerator ThermalMetric
open scoped ComplexConjugate
variable {n : ℕ} (S : Space (Fock n))

theorem OAI.ThermalSpectral.Space.weakDefect_centered {ρ : State n} (X : WeightedColumns ρ) (hI : X.Index=S.I)
    (x : S.I → Fock n) (hx : Summable (fun r => ‖x r‖^2))
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (S.p r):ℂ) • S.basis r)
    (he : HEq X.vector x) (j : Fin n) (μ : ℂ)
    (hd : Summable (fun a : S.I × S.I =>
      (1-frequency S.r (S.p a.1) (S.p a.2))*defectCoefficient S.r (S.p a.1) (S.p a.2)*
        ‖centeredEntry S.basis S.p x j μ a.1 a.2‖^2))
    (hc : HasSum (fun r => (S.p r:ℂ)*centeredEntry S.basis S.p x j μ r r) 0)
    (Z : Fock n →L[ℂ] Fock n) :
    weakDefect S.r x j μ Z=X.centeredWeak S.r j Z := by sorry
