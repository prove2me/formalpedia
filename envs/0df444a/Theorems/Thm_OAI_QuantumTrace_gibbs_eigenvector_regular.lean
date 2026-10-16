-- Prove2me | Theorems.Thm_OAI_QuantumTrace_gibbs_eigenvector_regular
-- name    : OAI.QuantumTrace.gibbs_eigenvector_regular
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:00:00.154207+00:00
-- url     : https://prove2.me/theorems/84223631-e0a4-4d67-aec3-9d04be8432da
-- title:
--   Weighted $\ell^2$ regularity of eigenvectors of a regularized Gibbs-type inverse
-- statement:
--   Let $\iota$ be an index set and $\ell^2(\iota)$ the Hilbert space of square-summable complex sequences. Let $s:\iota\to\mathbb{R}$ satisfy $s_i\ge 1$ for all $i$, and for $m\in\mathbb{N}$ let $D_m$ be the bounded diagonal operator $(D_mx)_i=s_i^{-m}x_i$. For $k>0$ and a positive bounded operator $B$ on $\ell^2(\iota)$, set
--   $$A=k\,I+D_3BD_3,\qquad G=D_4A^{-1}D_4 .$$
--   Let $u>0$ and let $\psi\in\ell^2(\iota)$ be a unit vector with $G\psi=u^{-1}\psi$. Then the weighted sequences $y_i=s_i^4\psi_i$ and $z_i=s_i^7\psi_i$ belong to $\ell^2(\iota)$ and satisfy
--   $$\|y\|^2\le\frac{u}{k},\qquad \|z\|\le\frac{1}{k}\Big(u+\|B\|\sqrt{u/k}\Big).$$
--
--   So an eigenvector of $G$ with eigenvalue $u^{-1}$ has explicit, quantitative decay against the weights $s_i^4$ and $s_i^7$, controlled by $u$, $k$ and $\|B\|$. With $s_i$ a power of a photon number, this gives finite higher photon-number moments for the spectral vectors of a regularized Gibbs construction.
--
--   **Formalization Note** $D_m$ is `inversePower s hs m`, $A$ is `gibbsFactor s hs k B`, and $G$ is `gibbsInverse s hs k B`, where $A^{-1}$ is `Ring.inverse A`. For $k>0$ and $B$ positive, $A$ is strictly positive and hence invertible, so `Ring.inverse` is the genuine inverse. The conclusion asserts the existence of vectors $y,z\in\ell^2(\iota)$ with the stated coordinates.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/QuantumTrace/Basic.lean#L1084-L1160

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic

open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open Filter Topology
variable {ι : Type*}

theorem OAI.QuantumTrace.gibbs_eigenvector_regular (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i)
    {k u : ℝ} (hk : 0 < k) (hu : 0 < u)
    {B : SequenceHilbert ι →L[ℂ] SequenceHilbert ι} (hB : B.IsPositive)
    {ψ : SequenceHilbert ι} (hψ : ‖ψ‖ = 1)
    (he : gibbsInverse s hs k B ψ = ((u⁻¹ : ℝ) : ℂ) • ψ) :
    ∃ y z : SequenceHilbert ι,
      (∀ i, y i = (s i^4 : ℝ)*ψ i) ∧
      (∀ i, z i = (s i^7 : ℝ)*ψ i) ∧
      ‖y‖^2 ≤ u/k ∧
      ‖z‖ ≤ k⁻¹*(u+‖B‖*Real.sqrt (u/k)) := by sorry
