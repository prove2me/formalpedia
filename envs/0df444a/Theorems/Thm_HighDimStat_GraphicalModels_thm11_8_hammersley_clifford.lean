-- Prove2me | Theorems.Thm_HighDimStat_GraphicalModels_thm11_8_hammersley_clifford
-- name    : HighDimStat.GraphicalModels.thm11_8_hammersley_clifford
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T23:21:03.998424+00:00
-- url     : https://prove2.me/theorems/ddb60b65-6911-49fc-bffd-b69662ffc30e
-- title:
--   The Hammersley-Clifford theorem (Theorem 11.8)
-- statement:
--   **Theorem 11.8 (Hammersley-Clifford)** (p. 351). For a given undirected graph $G$ and any
--   random vector $X=(X_1,\dots,X_d)$ with strictly positive density $p$, the following two
--   properties are equivalent: (a) $X$ factorizes according to the structure of $G$
--   (Definition 11.1); (b) $X$ is Markov with respect to $G$ (Definition 11.5).
--
--   This is the foundational equivalence underlying every graphical-model definition used
--   later in the chapter: it justifies treating "the graph encodes the conditional-independence
--   structure of $X$" and "the graph encodes a factorization of $X$'s density" as the same
--   object, which is what makes the precision-matrix-support characterization of a Gaussian
--   graphical model (Example 11.3) legitimate.
--
--   **Formalization Note** The book's proof establishes only the factorization $\Rightarrow$
--   Markov direction and cites the converse; the *statement* itself, formalized here, is the
--   full equivalence. The strict positivity of the density is essential — it is exactly what
--   the book's own remarks identify as necessary for the converse direction.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 351 (PDF p. 371), Theorem 11.8

import Mathlib
import Definitions.Def_HighDimStat_GraphicalModels_Core

namespace HighDimStat.GraphicalModels

open MeasureTheory

/-- **Theorem 11.8** (Hammersley-Clifford, p. 351, PDF 371). For a given undirected graph `G`
and any random vector `X = (X_1,…,X_d)` with strictly positive density `p` (with respect to
Lebesgue measure on `ℝ^V`), the following two properties are equivalent: (a) `X` factorizes
according to the structure of `G` (Definition 11.1); (b) `X` is Markov with respect to `G`
(Definition 11.5). -/
theorem thm11_8_hammersley_clifford {V Ω : Type*} [Fintype V] [DecidableEq V]
    [MeasurableSpace Ω] [StandardBorelSpace Ω] (G : SimpleGraph V) (X : Ω → V → ℝ)
    (hX : Measurable X) (P : Measure Ω) [IsProbabilityMeasure P]
    (p : (V → ℝ) → ℝ) (hp : ∀ x, 0 < p x)
    (hpdensity : Measure.map X P =
        (MeasureTheory.volume : Measure (V → ℝ)).withDensity (fun x => ENNReal.ofReal (p x))) :
    Factorizes G p ↔ IsMarkov G X hX P := by sorry

end HighDimStat.GraphicalModels
