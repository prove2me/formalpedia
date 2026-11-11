-- Prove2me | Theorems.Thm_GaussPolyReg_Approx_lemma_3_4
-- name    : GaussPolyReg.Approx.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:42:52.828045+00:00
-- url     : https://prove2.me/theorems/fd85009a-ab5e-49c5-b03b-44107bda9e45
-- title:
--   Lemma 3.4 — continuous bilinear top product on the ultraproduct
-- statement:
--   For a nonprincipal $U$ and $r,s\in\mathbb N$, coordinatewise top product induces
--
--   $$\diamond:\mathcal H_r\times\mathcal H_s\longrightarrow\mathcal H_{r+s}$$
--
--   as a well-defined jointly continuous real bilinear map. In particular, products of bounded homogeneous sequences remain bounded and homogeneous; equivalent inputs give equivalent outputs; additivity and scalar linearity hold in both variables. Joint continuity is the full two-variable epsilon-delta condition in the ultranorms. This justifies forming the primitive decomposition and iterating top products.
--
--   Differences from the source:
--   - encoding: the top product as a well-defined continuous bilinear map on homogeneous quotient spaces → bounded homogeneous representative sequences, equality by norm tending to zero along U, both variable linearities, and joint continuity in the ultranorm; reason: these assertions express the induced quotient map and its continuity without assuming an ultraproduct Hilbert-space instance
-- source:
--   Chris Jones, Regularity lemma for Gaussian polynomials, STOC 2027 submission #1637 (October 2026), Lemma 3.4, p. 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1637.pdf

import Mathlib
import Definitions.Def_GaussPolyReg_Approx_Ultra

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace GaussPolyReg.Approx

theorem lemma_3_4 (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite) (r s : ℕ) :
    (∀ p q, boundedHom r p → boundedHom s q → boundedHom (r+s) (seqTop r s p q)) ∧
    (∀ p p' q q', boundedHom r p → boundedHom r p' → boundedHom s q → boundedHom s q' →
      sameClass U p p' → sameClass U q q' →
      sameClass U (seqTop r s p q) (seqTop r s p' q')) ∧
    (∀ p p' q, boundedHom r p → boundedHom r p' → boundedHom s q →
      sameClass U (seqTop r s (p+p') q) (seqTop r s p q + seqTop r s p' q)) ∧
    (∀ (a : ℝ) p q, boundedHom r p → boundedHom s q →
      sameClass U (seqTop r s (a • p) q) (a • seqTop r s p q)) ∧
    (∀ p q q', boundedHom r p → boundedHom s q → boundedHom s q' →
      sameClass U (seqTop r s p (q+q')) (seqTop r s p q + seqTop r s p q')) ∧
    (∀ (a : ℝ) p q, boundedHom r p → boundedHom s q →
      sameClass U (seqTop r s p (a • q)) (a • seqTop r s p q)) ∧
    (∀ p₀ q₀, boundedHom r p₀ → boundedHom s q₀ → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ p q, boundedHom r p → boundedHom s q →
        ultraNorm U (p-p₀) < δ → ultraNorm U (q-q₀) < δ →
        ultraNorm U (seqTop r s p q - seqTop r s p₀ q₀) < ε) := by sorry

end GaussPolyReg.Approx
