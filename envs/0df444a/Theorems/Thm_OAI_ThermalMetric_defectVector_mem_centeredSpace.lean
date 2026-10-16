-- Prove2me | Theorems.Thm_OAI_ThermalMetric_defectVector_mem_centeredSpace
-- name    : OAI.ThermalMetric.defectVector_mem_centeredSpace
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:31:23.518385+00:00
-- url     : https://prove2.me/theorems/1a28f2dd-656e-4989-964b-e80d7b700d17
-- title:
--   Defect vectors of matrices with vanishing weighted diagonal trace lie in the centered subspace
-- statement:
--   Fix $r > 0$, an index set $J$ and a summable family $p : J \to (0,\infty)$. Put $h(r) = \log(r+1) - \log r > 0$ and, for $p, q > 0$,
--   $$
--   \phi_r(p,q) = \frac{\log p - \log q}{h(r)}, \qquad \delta_r(p,q) = (r+1)q - rp, \qquad m_r(p,q) = h(r)\,L(p,q)\,\omega_r\big(\phi_r(p,q)\big),
--   $$
--   where $L(p,q)$ is the logarithmic mean ($\frac{p-q}{\log p - \log q}$ for $p \neq q$, $L(p,p) = p$), $\omega_r(v) = \frac{1}{h(r)}\,\frac{f(h(r)v/2)\,f(-h(r)/2)}{f(h(r)(v-1)/2)}$ and $f(y) = y/\sinh y$ ($f(0) = 1$). The coefficient $m_r(p,q)$ is positive. For $a = (l, l') \in J \times J$ abbreviate $\phi_a = \phi_r(p_l, p_{l'})$, and similarly $\delta_a$, $m_a$.
--
--   Let $d : J \times J \to \mathbb{C}$ satisfy $\sum_a (1 - \phi_a)\,\delta_a\,|d_a|^2 < \infty$ (summable). Its *defect vector* is $D_d \in \ell^2(J \times J)$, $(D_d)_a = \dfrac{\delta_a}{\sqrt{m_a}}\, d_a$. The *identity vector* $E \in \ell^2(J\times J)$ has entries $E_{(l,l')} = \sqrt{m_{(l,l')}}$ if $l = l'$ and $0$ otherwise, and the *centered space* is $\mathcal C = \{u \in \ell^2(J \times J) : \langle E, u\rangle = 0\}$.
--
--   **Theorem.** If $\sum_{j \in J} p_j\, d(j,j) = 0$ (the series converging to $0$), then
--   $$
--   D_d \in \mathcal C, \qquad\text{i.e.}\qquad \langle E, D_d \rangle = 0 .
--   $$
--
--   In the thermal-metric picture, $J$ indexes an eigenbasis of a density operator with eigenvalues $p_j$, $m_r$ defines a weighted $\ell^2$ geometry on matrices, and $\mathcal C$ is the orthogonal complement of the identity matrix in this geometry. The lemma says that a matrix whose $p$-weighted diagonal trace vanishes yields a defect vector in $\mathcal C$, which is the domain on which the defect functionals are defined.
--
--   **Formalization Note** $h$, $\phi_r$, $\delta_r$, $m_r$ are `ThermalMetric.h`, `frequency`, `defectCoefficient`, `metricCoefficient` (with $\omega_r$ = `weight r` built from `fourWeightTarget` and `f`); $D_d$ is `defectVector r hr p hp d hd`, $E$ is `identityVector`, $\mathcal C$ is `centeredSpace r hr p hp hs`, the kernel of $u \mapsto \langle E, u\rangle$. The hypothesis on $d$ is the `HasSum` statement `HasSum (fun j => (p j : ℂ) * d (j,j)) 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/ThermalMetric.lean#L256-L280

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

open OAI OAI.ThermalMetric
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped ComplexConjugate
variable {J : Type*}

theorem OAI.ThermalMetric.defectVector_mem_centeredSpace (r : ℝ) (hr : 0<r) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : Summable p) (d : J × J → ℂ) (hd)
    (hc : HasSum (fun j => (p j:ℂ)*d (j,j)) 0) :
    defectVector r hr p hp d hd ∈ centeredSpace r hr p hp hs := by sorry
