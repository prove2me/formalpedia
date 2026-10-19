-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_polar_crossBins_error_le
-- name    : OAI.ThresholdParallelRepetition.QuantumSampling.polar_crossBins_error_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:51:22.027655+00:00
-- url     : https://prove2.me/theorems/a87ac7b7-1bda-4823-9cc4-b02357c7d7b3
-- title:
--   Approximating a matrix by its polar factor times bin-matched cross projections
-- statement:
--   Let $n$ be a finite index set, $M,N$ complex $n\times n$ matrices, and $\|X\|_{\mathrm{HS}}^2=\sum_{i,j}|X_{ij}|^2$. Let $|M|=\sqrt{M^*M}$, let $|M|^{+}$ be its support inverse (the Moore–Penrose pseudoinverse), $\mathrm{polar}(M)=M|M|^{+}$, and $|N|=\sqrt{N^*N}$. Fix $\varepsilon>0$, $s\in\mathbb R$ and a finite set $L\subset\mathbb Z$. For $l\in\mathbb Z$ let $\chi_l(t)=1$ if $t>0$ and $\lfloor\log t/\varepsilon+s\rfloor=l$ (and $0$ otherwise), and let $P_l(X)=\chi_l(X)$ be the spectral projection of a positive semidefinite $X$ onto its eigenvalues in the logarithmic bin $l$. Define the cross-bin matrix and the bin mismatch
--   $$
--   X_L=\sum_{l\in L}e^{\varepsilon(l-s)}\,P_l(|M|)\,P_l(|N|),\qquad\Delta_L=\sum_{l\in L}e^{2\varepsilon(l-s)}\,\big\|P_l(|M|)-P_l(|N|)\big\|_{\mathrm{HS}}^2 .
--   $$
--
--   **Theorem.** If every positive eigenvalue $a$ of $|M|$ satisfies $\lfloor\log a/\varepsilon+s\rfloor\in L$ (that is, $L$ covers the bins of $|M|$), then
--   $$
--   \big\|M-\mathrm{polar}(M)\,X_L\big\|_{\mathrm{HS}}^2\le2\varepsilon^2\,\|M\|_{\mathrm{HS}}^2+2\,\Delta_L .
--   $$
--
--   The matrix $\mathrm{polar}(M)X_L$ uses $|M|$ only through its bin projections, combined bin by bin with those of $|N|$. The estimate says that it reproduces $M$ up to the rounding error $\varepsilon\|M\|_{\mathrm{HS}}$ and a term measuring how differently $|M|$ and $|N|$ distribute over the bins. It is one of the error estimates of the quantum sampling (correlated sampling) part of the proof.
--
--   **Formalization Note** $X_L$ is `crossBins L (rightAbs M) (rightAbs N) ε s`, $\Delta_L$ is `binMismatch L (rightAbs M) (rightAbs N) ε s`, and the covering hypothesis is `CoversBins L (rightAbs M) ε s`. No hypothesis on $N$ is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/CoherentFilters.lean#L316-L335

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

theorem OAI.ThresholdParallelRepetition.QuantumSampling.polar_crossBins_error_le (L : Finset ℤ) (M N : Matrix n n ℂ)
    {ε : ℝ} (hε : 0 < ε) (s : ℝ) (hL : CoversBins L (rightAbs M) ε s) :
    hsSq (M-polar M*crossBins L (rightAbs M) (rightAbs N) ε s) ≤
      2*ε^2*hsSq M + 2*binMismatch L (rightAbs M) (rightAbs N) ε s := by sorry
