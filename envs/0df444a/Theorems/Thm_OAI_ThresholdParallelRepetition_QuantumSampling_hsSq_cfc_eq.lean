-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_hsSq_cfc_eq
-- name    : OAI.ThresholdParallelRepetition.QuantumSampling.hsSq_cfc_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:46:53.394136+00:00
-- url     : https://prove2.me/theorems/f7936041-302c-426d-81c1-c499276b2ee9
-- title:
--   Hilbert–Schmidt norm of a function of a Hermitian matrix
-- statement:
--   Let $n$ be a finite index set and $\|M\|_{\mathrm{HS}}^2=\sum_{i,j}|M_{ij}|^2$ the squared Hilbert–Schmidt (Frobenius) norm of a complex matrix $M$. Let $A$ be a Hermitian $n\times n$ complex matrix with eigenvalues $\lambda_i$, $i\in n$ (listed with multiplicity), and spectral decomposition $A=U\operatorname{diag}(\lambda_i)U^*$ with $U$ unitary. For any function $f:\mathbb R\to\mathbb R$ let $f(A)=U\operatorname{diag}(f(\lambda_i))U^*$ be given by the functional calculus. Then
--   $$
--   \|f(A)\|_{\mathrm{HS}}^2=\sum_{i}f(\lambda_i)^2 .
--   $$
--
--   For $f=\mathrm{id}$ this is $\|A\|_{\mathrm{HS}}^2=\sum_i\lambda_i^2$, and for $f(t)=t-w(t)$ it computes the Hilbert–Schmidt error of replacing $A$ by a spectrally modified matrix $w(A)$. Such identities reduce matrix estimates for spectral roundings to scalar estimates on eigenvalues.
--
--   **Formalization Note** The eigenvalues are `hA.eigenvalues` (indexed by `n`), $f(A)$ is `cfc f A`, and $\|\cdot\|_{\mathrm{HS}}^2$ is `hsSq`. No continuity of $f$ is needed because the spectrum is finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/SpectralBins.lean#L212-L226

import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt
import Definitions.Def_OAI_Probability_EntangledGames_SpectralBins

open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.QuantumSampling
universe u_n u_ι
open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open MeasureTheory Set
open scoped Interval
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix MeasureTheory
variable {n : Type u_n} [Fintype n] [DecidableEq n]

theorem OAI.ThresholdParallelRepetition.QuantumSampling.hsSq_cfc_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    hsSq (cfc f A) = ∑ i, (f (hA.eigenvalues i))^2 := by sorry
