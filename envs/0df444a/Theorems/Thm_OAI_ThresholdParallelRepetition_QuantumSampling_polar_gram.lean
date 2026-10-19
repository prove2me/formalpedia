-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_polar_gram
-- name    : OAI.ThresholdParallelRepetition.QuantumSampling.polar_gram
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:48:53.388187+00:00
-- url     : https://prove2.me/theorems/6ba9a30a-ff9b-457c-a532-bc62da72291d
-- title:
--   Gram matrix of the polar factor is the support projection of $|M|$
-- statement:
--   Let $m,n$ be finite index sets and $M\in\mathbb C^{m\times n}$. Let $|M|=\sqrt{M^*M}$ be the positive semidefinite square root of $M^*M$ (an $n\times n$ matrix), and let $|M|^{+}$ be its support inverse, obtained from the spectral decomposition of $|M|$ by inverting the nonzero eigenvalues and sending the eigenvalue $0$ to $0$ (the Moore–Penrose pseudoinverse). The polar factor of $M$ is
--   $$
--   \mathrm{polar}(M)=M\,|M|^{+}\in\mathbb C^{m\times n}.
--   $$
--   Then
--   $$
--   \mathrm{polar}(M)^*\,\mathrm{polar}(M)=|M|^{+}\,|M| .
--   $$
--
--   The right-hand side is the orthogonal projection onto the range of $|M|$, so $\mathrm{polar}(M)$ is a partial isometry and in particular a contraction, $\mathrm{polar}(M)^*\mathrm{polar}(M)\preceq I$. This is used to control Hilbert–Schmidt norms after multiplication by the polar factor and to compute Gram matrices of spectral filters built from it.
--
--   **Formalization Note** $|M|$ is `rightAbs M`, defined as `CFC.sqrt (Mᴴ * M)`, and $\mathrm{polar}(M)$ is `polar M = M * supportInverse (rightAbs M)`, where `supportInverse` is the functional calculus of $t\mapsto t^{-1}$ with Lean's convention that the inverse of $0$ is $0$. Only the column index type needs decidable equality.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/CoherentFilters.lean#L51-L65

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
open ThresholdParallelRepetition.MeasurementTransport
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n] [DecidableEq n]

theorem OAI.ThresholdParallelRepetition.QuantumSampling.polar_gram (M : Matrix m n ℂ) :
    (polar M)ᴴ * polar M = supportInverse (rightAbs M) * rightAbs M := by sorry
