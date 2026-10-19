-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_binFilter_contraction
-- name    : OAI.ThresholdParallelRepetition.QuantumSampling.binFilter_contraction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:50:17.869469+00:00
-- url     : https://prove2.me/theorems/b31180b3-3c02-49f3-8f8b-1903f2140624
-- title:
--   The spectral-bin filter of a polar factor is a contraction
-- statement:
--   Let $n$ be a finite index set, $M$ an $n\times n$ complex matrix, $L\subset\mathbb Z$ a finite set of bin labels, and $\varepsilon,s\in\mathbb R$. Let $|M|=\sqrt{M^*M}$, let $|M|^{+}$ be its support inverse (the Moore–Penrose pseudoinverse) and $\mathrm{polar}(M)=M|M|^{+}$. For $l\in\mathbb Z$ let $\chi_l(t)=1$ if $t>0$ and $\lfloor\log t/\varepsilon+s\rfloor=l$, and $\chi_l(t)=0$ otherwise, and let
--   $$
--   P_l=\chi_l(|M|)
--   $$
--   be the spectral projection of $|M|$ onto its eigenvalues in the logarithmic bin $l$. The bin filter is the $n\times(n\times L)$ matrix
--   $$
--   W=\big[\ \mathrm{polar}(M)\,P_l\ \big]_{l\in L},\qquad W_{i,(j,l)}=\big(\mathrm{polar}(M)\,P_l\big)_{ij},
--   $$
--   the block row with blocks $\mathrm{polar}(M)P_l$, which maps $\bigoplus_{l\in L}\mathbb C^n$ to $\mathbb C^n$.
--
--   **Theorem.** For every finite $L\subset\mathbb Z$, every $M$ and all real $\varepsilon,s$,
--   $$
--   W^*W\preceq I_{n\times L},
--   $$
--   where $\preceq$ is the Loewner order on Hermitian matrices indexed by $n\times L$.
--
--   Equivalently $\|Wv\|\le\|v\|$ for every vector $v$: the bin filter is a contraction, so it can serve as a local filtering operator when the polar part of $M$ is split according to the logarithmic bins of $|M|$. Contractions of this kind satisfy the hypotheses of the Hilbert–Schmidt mass bounds for filtered bipartite states.
--
--   **Formalization Note** $W$ is `binFilter L M ε s`, a `Matrix n (n × L) ℂ` whose columns are indexed by pairs $(j,l)$, and $P_l$ is `binProjection (rightAbs M) ε s l`, the functional calculus of `binIndicator ε s l`. No hypotheses on $\varepsilon$ or $s$ are needed; for $\varepsilon=0$ Lean's convention $x/0=0$ merely makes the binning degenerate.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/CoherentFilters.lean#L145-L157

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
variable {n : Type u_n} [Fintype n] [DecidableEq n]

theorem OAI.ThresholdParallelRepetition.QuantumSampling.binFilter_contraction (L : Finset ℤ) (M : Matrix n n ℂ) (ε s : ℝ) :
    (binFilter L M ε s)ᴴ * binFilter L M ε s ≤ 1 := by sorry
