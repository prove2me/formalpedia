-- Prove2me | Theorems.Thm_OAI_ThermalSpectral_diagram_comparison
-- name    : OAI.ThermalSpectral.diagram_comparison
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:24:18.916683+00:00
-- url     : https://prove2.me/theorems/013816fe-dc5c-4f4a-8571-25677aac861a
-- title:
--   Operator-level weighted inequalities give a diagonal-form comparison for the thermal diagram
-- statement:
--   A *thermal spectral datum* $\mathcal S=(e,p,r)$ on a complex Hilbert space $E$ consists of a Hilbert basis $(e_k)_{k\in I}$ of $E$, weights $p_k>0$ with $\sum_k p_k=1$, and a parameter $r>0$. Put $h(r)=\log(r+1)-\log r$, write $L(a,b)$ for the logarithmic mean ($L(a,b)=\frac{b-a}{\log b-\log a}$ if $a\neq b$ and $L(a,a)=a$), and set $\nu_{kl}=\frac{\log p_k-\log p_l}{h(r)}$. For a weight $X:(0,\infty)\times\mathbb{R}\to\mathbb{R}$ and a bounded operator $T$ on $E$ define
--   $$Q^{\mathcal S}_X(T)=\sum_{k,l\in I} X(r,\nu_{kl})\,h(r)\,L(p_k,p_l)\,\bigl|\langle e_k,Te_l\rangle\bigr|^2 .$$
--   Let $\mathcal Z(\mathcal S)$ be the complex linear span of the centered matrix units $G_{kl}=|e_k\rangle\langle e_l|-\delta_{kl}\,p_k\,\mathrm{Id}$.
--
--   Fix three thermal spectral data $\mathcal S_0$ and $\mathcal S_1,\mathcal S_2$ on $E$ (with bases $e^{(i)}$, weights $p^{(i)}$, parameters $r_i$), nonnegative numbers $w_1,w_2\ge0$, complex-linear maps $L_1,L_2$ from bounded operators on $E$ to bounded operators on $E$, and a weight $X\ge0$. The associated *diagram* is the diagonal-form system whose test vectors are the coordinate arrays $z_{kl}=\sqrt{h(r_0)L(p^{(0)}_k,p^{(0)}_l)}\,\langle e^{(0)}_k,Ze^{(0)}_l\rangle$ of operators $Z\in\mathcal Z(\mathcal S_0)$, with source parameter $(r_0,\nu^{(0)}_{kl})$ at the index $(k,l)$; whose target indices are pairs $(i,(a,b))$ with $i\in\{1,2\}$ and $a,b$ in the index set of $\mathcal S_i$, with parameter $(r_i,\nu^{(i)}_{ab})$; and whose linear map sends $z$ (that is, the unique operator $Z$ with these coordinates) to
--   $$(Dz)_{i,(a,b)}=\sqrt{w_i}\,\sqrt{h(r_i)L(p^{(i)}_a,p^{(i)}_b)}\;\bigl\langle e^{(i)}_a,(L_iZ)\,e^{(i)}_b\bigr\rangle .$$
--   The diagram *satisfies the comparison for $X$* if for every test vector $z$ and every finite set $s$ of target indices
--   $$\sum_{(i,(a,b))\in s} X\bigl(r_i,\nu^{(i)}_{ab}\bigr)\,\bigl|(Dz)_{i,(a,b)}\bigr|^2\;\le\;\sum_{k,l} X\bigl(r_0,\nu^{(0)}_{kl}\bigr)\,|z_{kl}|^2 .$$
--
--   **Theorem.** Suppose that for each $i\in\{1,2\}$ and every bounded operator $T$ the series defining $Q^{\mathcal S_i}_X(T)$ converges, and that for every $Z\in\mathcal Z(\mathcal S_0)$
--   $$\sum_{i=1}^{2} w_i\,Q^{\mathcal S_i}_X(L_iZ)\;\le\;Q^{\mathcal S_0}_X(Z).$$
--   Then the diagram built from $\mathcal S_0,\mathcal S_1,\mathcal S_2,w,L$ satisfies the comparison for $X$.
--
--   This converts a concrete inequality between weighted Hilbert–Schmidt-type quadratic forms of operators into the abstract "comparison" format used by the four-weight interpolation theorem for positive diagonal quadratic forms, so that operator inequalities for several weights can be fed into that theorem.
--
--   **Formalization Note** The structure `ThermalSpectral.Space` packages $(e,p,r)$, `Space.pquad X` is $Q^{\mathcal S}_X$ (an infinite `tsum`), `diagram` builds a `DiagonalForms.System` over the parameter type $\{r>0\}\times\mathbb{R}$, and `Comparison X` is the finite-target-sum inequality displayed above.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/SpectralForms.lean#L732-L764

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

open OAI OAI.ThermalSpectral
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
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem OAI.ThermalSpectral.diagram_comparison (S₀ : Space E) (S : Fin 2 → Space E) (w : Fin 2 → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (L : (i : Fin 2) → (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E)) (X : Param → ℝ)
    (hX : ∀ q, 0 ≤ X q)
    (hs : ∀ i Z, Summable (fun a => X ((S i).pparam a)*Complex.normSq ((S i).coords Z a)))
    (he : ∀ Z, Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p →
      ∑ i, w i*(S i).pquad X (L i Z) ≤ S₀.pquad X Z) :
    (diagram S₀ S w L).Comparison X := by sorry
