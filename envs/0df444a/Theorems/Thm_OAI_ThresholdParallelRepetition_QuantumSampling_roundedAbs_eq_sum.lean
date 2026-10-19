-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_roundedAbs_eq_sum
-- name    : OAI.ThresholdParallelRepetition.QuantumSampling.roundedAbs_eq_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:50:49.474405+00:00
-- url     : https://prove2.me/theorems/9f19a6d4-87e2-43eb-87cf-a9be49138316
-- title:
--   Spectral rounding as a combination of bin projections
-- statement:
--   Let $n$ be a finite index set, $A$ an $n\times n$ complex matrix, $\varepsilon,s\in\mathbb R$, and $L\subset\mathbb Z$ a finite set. For $l\in\mathbb Z$ define the bin scale $c_l=e^{\varepsilon(l-s)}$, the bin indicator $\chi_l(t)=1$ if $t>0$ and $\lfloor\log t/\varepsilon+s\rfloor=l$ (and $\chi_l(t)=0$ otherwise), and the bin projection $P_l(A)=\chi_l(A)$. Let $w(t)=e^{\varepsilon(\lfloor\log t/\varepsilon+s\rfloor-s)}$ for $t>0$ and $w(t)=0$ for $t\le0$ (rounding down to the geometric grid of the $c_l$), and let the rounded matrix be $R(A)=w(A)$; here $f(A)$ denotes the functional calculus. Say that $L$ covers the bins of $A$ if $\lfloor\log a/\varepsilon+s\rfloor\in L$ for every positive real number $a$ in the spectrum of $A$.
--
--   **Theorem.** If $L$ covers the bins of $A$, then
--   $$
--   R(A)=\sum_{l\in L}e^{\varepsilon(l-s)}\,P_l(A).
--   $$
--
--   For Hermitian $A$ the $P_l(A)$ are mutually orthogonal spectral projections, so this exhibits the spectral rounding of $A$ as a finite orthogonal combination of projections with the grid values as coefficients. This form allows the rounding of one matrix to be compared, bin by bin, with the bin projections of another matrix.
--
--   **Formalization Note** $R(A)$ is `roundedAbs A ε s`, i.e. `cfc (fun a => binWeight a ε s) A`; $P_l(A)$ is `binProjection A ε s l`, $c_l$ is `binScale ε s l`, and the covering hypothesis is `CoversBins L A ε s`, phrased with `spectrum ℝ A`. No self-adjointness of $A$ is assumed: for a non-Hermitian matrix the real functional calculus is $0$ by convention and both sides vanish. The sum runs over the elements of the finset `L`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/CoherentFilters.lean#L267-L281

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

open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.QuantumSampling
universe u_m u_n u_p u_ι u_q
open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped Interval
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
variable {n : Type u_n} [Fintype n] [DecidableEq n]

theorem OAI.ThresholdParallelRepetition.QuantumSampling.roundedAbs_eq_sum (L : Finset ℤ) {A : Matrix n n ℂ} (ε s : ℝ)
    (hL : CoversBins L A ε s) :
    roundedAbs A ε s = ∑ l : L, binScale ε s l • binProjection A ε s l := by sorry
