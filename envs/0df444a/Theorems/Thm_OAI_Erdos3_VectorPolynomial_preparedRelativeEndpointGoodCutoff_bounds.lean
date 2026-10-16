-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedRelativeEndpointGoodCutoff_bounds
-- name    : OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointGoodCutoff_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-16T01:54:06.042003+00:00
-- url     : https://prove2.me/theorems/d7d711d7-ff71-4953-99de-1206b5fbe366
-- title:
--   Bounds on the relative-endpoint good cutoff ⌈exp(2P)⌉ and its log 2P+1
-- statement:
--   Let $P_{\mathrm{test}}$ be a real number with $P_{\mathrm{test}} \ge 0$. Write $\ell = $ `preparedRelativeEndpointGoodLog Ptest` $= 2P_{\mathrm{test}} + 1$ and $K = $ `preparedRelativeEndpointGoodCutoff Ptest` $= \lceil e^{2P_{\mathrm{test}}} \rceil$ (natural-number ceiling). Then $0 \le \ell$, $1 \le K$, $e^{2P_{\mathrm{test}}} \le K$ and $K \le e^{\ell}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointGoodCutoff_bounds` in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeEndpointSourceBounds.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1327` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeEndpointSourceBounds.lean#L220

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1327

namespace OAI

section

namespace Erdos3

namespace VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

end AllocatedExternalCandidateSampler
end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    (sampler : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedRelativeEndpointGoodCutoff_bounds {Ptest : ℝ} (hPtest : 0 ≤ Ptest) :
    0 ≤ preparedRelativeEndpointGoodLog Ptest ∧
    1 ≤ preparedRelativeEndpointGoodCutoff Ptest ∧
    Real.exp (2 * Ptest) ≤ (preparedRelativeEndpointGoodCutoff Ptest : ℝ) ∧
    (preparedRelativeEndpointGoodCutoff Ptest : ℝ) ≤
      Real.exp (preparedRelativeEndpointGoodLog Ptest) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
