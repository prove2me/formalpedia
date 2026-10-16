-- Prove2me | Theorems.Thm_OAI_QuantumTrace_gibbs_fock_spectral_regular
-- name    : OAI.QuantumTrace.gibbs_fock_spectral_regular
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:00:40.355498+00:00
-- url     : https://prove2.me/theorems/cbd61cad-c73e-452c-b35e-7cab4140a71d
-- title:
--   Regular eigenbasis with summable heat trace for a regularized inverse on $\ell^2(\mathbb{N}^n)$
-- statement:
--   Let $n\in\mathbb{N}$, let $\ell^2(\mathbb{N}^n)$ be the Hilbert space of square-summable complex sequences indexed by multi-indices $i\in\mathbb{N}^n$, and let $s_i=\sqrt{1+|i|}$ with $|i|=i_1+\dots+i_n$. For $m\in\mathbb{N}$ let $D_m$ be the diagonal operator $(D_mx)_i=s_i^{-m}x_i$. Fix $k>0$ and a positive bounded operator $B$ on $\ell^2(\mathbb{N}^n)$, and set $A=kI+D_3BD_3$ and $G=D_4A^{-1}D_4$. Then there exist an index set $J$, a Hilbert basis $(b_j)_{j\in J}$ of $\ell^2(\mathbb{N}^n)$ and numbers $u_j$, $j\in J$, such that:
--
--   1. $u_j>0$ for every $j$;
--   2. $G\,b_j=u_j^{-1}\,b_j$ for every $j$;
--   3. for every $j$, the sequences $y_i=s_i^4\,b_j(i)=(1+|i|)^2\,b_j(i)$ and $z_i=s_i^7\,b_j(i)$ lie in $\ell^2(\mathbb{N}^n)$ and satisfy
--   $$\|y\|^2\le\frac{u_j}{k},\qquad \|z\|\le\frac{1}{k}\Big(u_j+\|B\|\sqrt{u_j/k}\Big);$$
--   4. for every $t>0$ the heat trace converges: $\sum_{j\in J}e^{-t\,u_j}<\infty$.
--
--   One may think of $G$ as the inverse of a positive operator $H$ with eigenvectors $b_j$ and eigenvalues $u_j$. The theorem provides a common eigenbasis together with the two facts needed to build Gibbs-type states $\propto e^{-tH}$ from it: the partition functions are finite for every $t>0$, and each eigenvector has quantitatively controlled photon-number moments.
--
--   **Formalization Note** $s$ is `rootNumberWeight`, $G$ is `gibbsInverse rootNumberWeight rootNumberWeight_one_le k B`, and $A^{-1}$ is `Ring.inverse`, which is the true inverse here because $A$ is strictly positive. The index type $J$ lives in `Type`. Item 3 is stated as the existence of $y,z\in\ell^2(\mathbb{N}^n)$ with the given coordinates.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/QuantumTrace/Basic.lean#L1327-L1358

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic

open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open Filter Topology

theorem OAI.QuantumTrace.gibbs_fock_spectral_regular (n : ℕ) {k : ℝ} (hk : 0 < k)
    {B : SequenceHilbert (Fin n → ℕ) →L[ℂ] SequenceHilbert (Fin n → ℕ)} (hB : B.IsPositive) :
    ∃ (J : Type) (b : HilbertBasis J ℂ (SequenceHilbert (Fin n → ℕ))) (u : J → ℝ),
      (∀ j, 0 < u j) ∧
      (∀ j, gibbsInverse rootNumberWeight rootNumberWeight_one_le k B (b j) = (((u j)⁻¹ : ℝ) : ℂ) • b j) ∧
      (∀ j, ∃ y z : SequenceHilbert (Fin n → ℕ),
        (∀ i, y i = (rootNumberWeight i^4 : ℝ)*b j i) ∧
        (∀ i, z i = (rootNumberWeight i^7 : ℝ)*b j i) ∧
        ‖y‖^2 ≤ u j/k ∧ ‖z‖ ≤ k⁻¹*(u j+‖B‖*Real.sqrt (u j/k))) ∧
      (∀ t : ℝ, 0 < t → Summable (fun j => Real.exp (-t*u j))) := by sorry
