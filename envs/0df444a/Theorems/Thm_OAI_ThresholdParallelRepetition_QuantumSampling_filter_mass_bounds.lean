-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_filter_mass_bounds
-- name    : OAI.ThresholdParallelRepetition.QuantumSampling.filter_mass_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:52:06.840261+00:00
-- url     : https://prove2.me/theorems/7abf7772-0b79-4295-ad64-541bc8e9568d
-- title:
--   Local contractions do not increase the Hilbert–Schmidt mass of a bipartite state
-- statement:
--   Let $m,n,p,q$ be finite index sets and $\|X\|_{\mathrm{HS}}^2=\sum_{i,j}|X_{ij}|^2$. Let $D\in\mathbb C^{n\times q}$, $K\in\mathbb C^{m\times n}$ and $L\in\mathbb C^{p\times q}$ be complex matrices with $K^*K\preceq I_n$ and $L^*L\preceq I_q$ in the Loewner order (that is, $K$ and $L$ are contractions), and let $L^{\mathsf T}$ denote the transpose of $L$ (not its conjugate transpose). Then:
--
--   1. $\|KDL^{\mathsf T}\|_{\mathrm{HS}}^2\le\|KD\|_{\mathrm{HS}}^2$;
--   2. $\|KDL^{\mathsf T}\|_{\mathrm{HS}}^2\le\|DL^{\mathsf T}\|_{\mathrm{HS}}^2$;
--   3. $\|KD\|_{\mathrm{HS}}^2\le\|D\|_{\mathrm{HS}}^2$;
--   4. $\|DL^{\mathsf T}\|_{\mathrm{HS}}^2\le\|D\|_{\mathrm{HS}}^2$.
--
--   To interpret these, identify $D$ with the bipartite vector $|D\rangle=\sum_{j,k}D_{jk}\,e_j\otimes e_k\in\mathbb C^n\otimes\mathbb C^q$, whose squared norm is $\|D\|_{\mathrm{HS}}^2$. Then
--   $$
--   (K\otimes L)\,|D\rangle=|KDL^{\mathsf T}\rangle,\qquad(K\otimes I)\,|D\rangle=|KD\rangle,\qquad(I\otimes L)\,|D\rangle=|DL^{\mathsf T}\rangle ,
--   $$
--   so the theorem says that local contractions (filters) applied by one or both parties never increase the squared norm, or mass, of a shared bipartite vector, and that the mass after filtering on both sides is at most the mass after filtering on either side. These bounds control the normalisation of filtered states in the quantum sampling argument.
--
--   **Formalization Note** The statement is the conjunction of the four inequalities for `hsSq`, with `Lᵀ` the transpose; the hypotheses are `Kᴴ*K ≤ 1` and `Lᴴ*L ≤ 1` in Mathlib's matrix order. All index types are finite with decidable equality.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/SamplingStrategy.lean#L327-L343

import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt
import Definitions.Def_OAI_Probability_EntangledGames_SpectralBins
import Definitions.Def_OAI_Probability_EntangledGames_CoherentFilters
import Definitions.Def_OAI_Probability_EntangledGames_SamplingStrategy

open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.QuantumSampling
universe u_n u_A u_m u_ι u_p u_q u_B
open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped Interval
open scoped Kronecker
variable {m : Type u_m} {n : Type u_n} {A : Type u_A} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [Fintype A]
variable {m : Type u_m} {n : Type u_n} {p : Type u_p} {q : Type u_q} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

theorem OAI.ThresholdParallelRepetition.QuantumSampling.filter_mass_bounds (D : Matrix n q ℂ) (K : Matrix m n ℂ) (L : Matrix p q ℂ)
    (hK : Kᴴ*K ≤ 1) (hL : Lᴴ*L ≤ 1) :
    hsSq (K*D*Lᵀ) ≤ hsSq (K*D) ∧ hsSq (K*D*Lᵀ) ≤ hsSq (D*Lᵀ) ∧
      hsSq (K*D) ≤ hsSq D ∧ hsSq (D*Lᵀ) ≤ hsSq D := by sorry
