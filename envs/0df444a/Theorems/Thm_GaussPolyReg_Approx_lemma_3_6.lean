-- Prove2me | Theorems.Thm_GaussPolyReg_Approx_lemma_3_6
-- name    : GaussPolyReg.Approx.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:42:59.279104+00:00
-- url     : https://prove2.me/theorems/3dbb437e-6326-4aa0-81b8-f9aa0ef7d972
-- title:
--   Lemma 3.6 — primitiveness iff proper flattenings vanish
-- statement:
--   Let $[p_n]\in\mathcal H_d$, with symmetric Hermite coefficient tensor $P_n$. Then
--
--   $$[p_n]\in\mathcal P_d\quad\Longleftrightarrow\quad\lim_{n\to U}\|P_n^{(r)}\|_{\rm op}=0\quad\text{for every }0<r<d.$$
--
--   Primitiveness means orthogonality to the closed span of all positive complementary-degree top products. Both implications are asserted for every nonprincipal ultrafilter. The norm is the Euclidean spectral norm. This connects the primitive space to the fourth-moment criterion.
--
--   Differences from the source:
--   - encoding: a homogeneous quotient class is primitive if and only if every proper coefficient-tensor flattening vanishes along U → a bounded homogeneous sequence is orthogonal along U to all complementary positive-degree top products if and only if all proper Euclidean spectral flattening norms tend to zero; reason: orthogonality to all generating products is equivalent to orthogonality to their closed linear span; coefficient tensors are computed from (3.3)
-- source:
--   Chris Jones, Regularity lemma for Gaussian polynomials, STOC 2027 submission #1637 (October 2026), Lemma 3.6, p. 9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1637.pdf

import Mathlib
import Definitions.Def_GaussPolyReg_Approx_Ultra

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace GaussPolyReg.Approx

theorem lemma_3_6 (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
    (d : ℕ) (p : Sequence) (hp : boundedHom d p) :
    primitive U d p ↔ ∀ r, 0 < r → r < d →
      Tendsto (fun n => flattenNorm (coefficientTensor (n := n) (d := d) (p n)) r)
        (U : Filter ℕ) (𝓝 0) := by sorry

end GaussPolyReg.Approx
