-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_exists_shift_spectralEnvelope_le
-- name    : OAI.ThresholdParallelRepetition.QuantumSampling.exists_shift_spectralEnvelope_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:47:27.32396+00:00
-- url     : https://prove2.me/theorems/d6c78ddc-0ef9-4100-8d84-36d4f0cd57d2
-- title:
--   A common shift of logarithmic spectral bins with small average envelope
-- statement:
--   Let $n$ be a finite index set and $\|M\|_{\mathrm{HS}}^2=\sum_{i,j}|M_{ij}|^2$. For Hermitian $n\times n$ complex matrices $A,B$ with spectral decompositions $A=U\operatorname{diag}(\lambda_i)U^*$ and $B=V\operatorname{diag}(\mu_j)V^*$ (as fixed by Mathlib, $U,V$ unitary) write $o_{ij}=|(U^*V)_{ij}|^2$ for the overlaps of their eigenvectors. For $\varepsilon>0$ and $s\in\mathbb R$ define:
--
--   1. the separation indicator of $u,v\in\mathbb R$: $\mathrm{sep}_s(u,v)=0$ if $\lfloor u+s\rfloor=\lfloor v+s\rfloor$, and $\mathrm{sep}_s(u,v)=1$ otherwise;
--   2. the bin envelope of $a,b\ge0$:
--   $$
--   \beta_{\varepsilon,s}(a,b)=(a-b)^2+2ab\;\mathrm{sep}_s\Big(\frac{\log a}{\varepsilon},\frac{\log b}{\varepsilon}\Big);
--   $$
--   3. the spectral envelope of $A,B$:
--   $$
--   \mathcal E_{\varepsilon,s}(A,B)=\sum_{i,j}\beta_{\varepsilon,s}(\lambda_i,\mu_j)\,o_{ij}.
--   $$
--
--   Thus $\mathrm{sep}_s(\log a/\varepsilon,\log b/\varepsilon)=1$ exactly when $a$ and $b$ lie in different logarithmic bins $\{t>0:\ \lfloor\log t/\varepsilon+s\rfloor=l\}$, and the envelope charges $2ab$ for every coupled pair of eigenvalues separated by a bin boundary.
--
--   **Theorem.** Let $\iota$ be a finite index set, $w_i\ge0$ weights with $\sum_iw_i=1$, and $A_i,B_i$ ($i\in\iota$) positive semidefinite $n\times n$ complex matrices with $\|A_i\|_{\mathrm{HS}}=\|B_i\|_{\mathrm{HS}}=1$. Let $0<\varepsilon\le1$. Then there is a shift $s\in\mathbb R$ such that
--   $$
--   \sum_{i}w_i\,\mathcal E_{\varepsilon,s}(A_i,B_i)\le\frac{6}{\varepsilon}\sqrt{\sum_iw_i\,\|A_i-B_i\|_{\mathrm{HS}}^2}\,.
--   $$
--
--   A single shift of the logarithmic bin grid therefore works simultaneously, on weighted average, for all pairs $(A_i,B_i)$, at a cost controlled by the average squared Hilbert–Schmidt distance. This is the choice of a common bin grid in the quantum sampling (correlated sampling) step, where two parties holding nearby normalized positive matrices round their spectra to shared bins.
--
--   **Formalization Note** $\mathrm{sep}$, $\beta$ and $\mathcal E$ are `separated`, `binEnvelope` and `spectralEnvelope`, the latter built from the eigenvalues and `eigenvectorUnitary` of the Hermitian matrices obtained from the positivity hypotheses; unit norm is stated as `hsSq (A i) = 1`. Lean's convention $\log0=0$ is harmless because the separation term is multiplied by $ab$. The statement only asserts the existence of some real $s$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/SpectralBins.lean#L374-L396

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
open scoped BigOperators MatrixOrder ComplexOrder Interval
open Matrix MeasureTheory
variable {n : Type u_n} [Fintype n] [DecidableEq n]

theorem OAI.ThresholdParallelRepetition.QuantumSampling.exists_shift_spectralEnvelope_le {ι : Type u_ι} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (A B : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hB : ∀ i, (B i).PosSemidef)
    (hAe : ∀ i, hsSq (A i) = 1) (hBe : ∀ i, hsSq (B i) = 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ s : ℝ, (∑ i, w i * spectralEnvelope (hA i).isHermitian (hB i).isHermitian ε s) ≤
      (6/ε) * Real.sqrt (∑ i, w i * hsSq (A i-B i)) := by sorry
