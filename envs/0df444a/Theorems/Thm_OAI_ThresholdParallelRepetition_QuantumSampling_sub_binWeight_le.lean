-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_sub_binWeight_le
-- name    : OAI.ThresholdParallelRepetition.QuantumSampling.sub_binWeight_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:45:36.892989+00:00
-- url     : https://prove2.me/theorems/7097d647-1926-47bb-a6d1-c447f7a2b8c9
-- title:
--   Rounding down to a geometric grid of ratio $e^{\varepsilon}$ loses at most an $\varepsilon$-fraction
-- statement:
--   For $\varepsilon>0$ and a shift $s\in\mathbb R$ define the bin weight of a real number $a$ by
--   $$
--   w_{\varepsilon,s}(a)=\begin{cases}\exp\Big(\varepsilon\big(\lfloor\log(a)/\varepsilon+s\rfloor-s\big)\Big), & a>0,\\ 0, & a\le0.\end{cases}
--   $$
--   For $a>0$ the number $\varepsilon(\lfloor\log a/\varepsilon+s\rfloor-s)$ is the largest point of the shifted grid $\varepsilon(\mathbb Z-s)$ not exceeding $\log a$, so $w_{\varepsilon,s}(a)$ is $a$ rounded down to the geometric grid $\{e^{\varepsilon(l-s)}:\ l\in\mathbb Z\}$.
--
--   **Theorem.** For all real numbers $a\ge0$, $\varepsilon>0$ and $s$,
--   $$
--   a-w_{\varepsilon,s}(a)\le\varepsilon\,a .
--   $$
--
--   Together with the companion bound $w_{\varepsilon,s}(a)\le a$ this says that rounding down to the grid has relative error at most $\varepsilon$, i.e. $(1-\varepsilon)a\le w_{\varepsilon,s}(a)\le a$. Applied to the eigenvalues of a positive semidefinite matrix $A$ through the functional calculus, it shows that the spectrally rounded matrix $w_{\varepsilon,s}(A)$ lies within Hilbert–Schmidt distance $\varepsilon\|A\|_{\mathrm{HS}}$ of $A$.
--
--   **Formalization Note** $w_{\varepsilon,s}(a)$ is `binWeight a ε s`, built from `Real.log`, `Real.exp` and the integer floor `Int.floor`. No upper bound on $\varepsilon$ is assumed; for $\varepsilon\ge1$ the statement already follows from $w_{\varepsilon,s}(a)\ge0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/SpectralBins.lean#L174-L191

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

theorem OAI.ThresholdParallelRepetition.QuantumSampling.sub_binWeight_le {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) (s : ℝ) :
    a - binWeight a ε s ≤ ε*a := by sorry
