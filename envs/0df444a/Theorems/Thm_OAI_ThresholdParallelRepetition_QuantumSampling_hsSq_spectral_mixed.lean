-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_hsSq_spectral_mixed
-- name    : OAI.ThresholdParallelRepetition.QuantumSampling.hsSq_spectral_mixed
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:44:56.246119+00:00
-- url     : https://prove2.me/theorems/5f3c1782-3908-4f3d-a28a-09b0b30d14b7
-- title:
--   Hilbert–Schmidt distance of $f(A)$ and $g(B)$ via eigenvector overlaps
-- statement:
--   Let $n$ be a finite index set and for a complex matrix $M$ let $\|M\|_{\mathrm{HS}}^2=\sum_{i,j}|M_{ij}|^2$ be its squared Hilbert–Schmidt (Frobenius) norm. Let $A,B$ be Hermitian $n\times n$ complex matrices with spectral decompositions
--   $$
--   A=U\operatorname{diag}(\lambda_1,\dots,\lambda_n)\,U^*,\qquad B=V\operatorname{diag}(\mu_1,\dots,\mu_n)\,V^*,
--   $$
--   where $U,V$ are unitary, their columns $u_i$, $v_j$ are orthonormal eigenvectors, and $\lambda_i,\mu_j\in\mathbb R$ are the eigenvalues (these are the decompositions fixed by Mathlib). For arbitrary functions $f,g:\mathbb R\to\mathbb R$ let $f(A)=U\operatorname{diag}(f(\lambda_i))U^*$ and $g(B)=V\operatorname{diag}(g(\mu_j))V^*$. Then
--   $$
--   \|f(A)-g(B)\|_{\mathrm{HS}}^2=\sum_{i,j}\big(f(\lambda_i)-g(\mu_j)\big)^2\,\big|(U^*V)_{ij}\big|^2=\sum_{i,j}\big(f(\lambda_i)-g(\mu_j)\big)^2\,|\langle u_i,v_j\rangle|^2 .
--   $$
--
--   Since $U^*V$ is unitary, the weights $|\langle u_i,v_j\rangle|^2$ form a doubly stochastic matrix, that is, a coupling of the spectra of $A$ and $B$, and the theorem expresses $\|f(A)-g(B)\|_{\mathrm{HS}}^2$ as the quadratic transport cost between $f(\lambda)$ and $g(\mu)$ under this coupling. With $f=g=\mathrm{id}$ it gives $\|A-B\|_{\mathrm{HS}}^2$ in spectral form, the basis of the estimates for rounding the spectra of nearby matrices into common bins.
--
--   **Formalization Note** The eigenvalues and the unitary are `hA.eigenvalues` and `hA.eigenvectorUnitary` (likewise for `B`), $f(A)$ is `cfc f A`, $|z|^2$ is `Complex.normSq z`, and $\|\cdot\|_{\mathrm{HS}}^2$ is `hsSq`. No continuity of $f,g$ is needed because spectra of matrices are finite. The inner product is $\langle u,v\rangle=u^*v$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/HilbertSchmidt.lean#L55-L91

import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt

open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.QuantumSampling
universe u_m u_n u_p u_q
open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {m : Type u_m} {n : Type u_n} {p : Type u_p} [Fintype m] [Fintype n] [Fintype p]

theorem OAI.ThresholdParallelRepetition.QuantumSampling.hsSq_spectral_mixed [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f g : ℝ → ℝ) :
    hsSq (cfc f A - cfc g B) =
      ∑ i, ∑ j, (f (hA.eigenvalues i) - g (hB.eigenvalues j)) ^ 2 *
        Complex.normSq (((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
          (hB.eigenvectorUnitary : Matrix n n ℂ)) i j) := by sorry
