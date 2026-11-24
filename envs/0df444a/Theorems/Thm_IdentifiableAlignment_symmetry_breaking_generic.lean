-- Prove2me | Theorems.Thm_IdentifiableAlignment_symmetry_breaking_generic
-- name    : IdentifiableAlignment.symmetry_breaking_generic
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T03:16:54.619397+00:00
-- url     : https://prove2.me/theorems/94091049-96cd-433c-95b3-719caa62a17e
-- title:
--   Proposition 3.2: symmetry breaking holds for an open dense set of densities
-- statement:
--   Let $(\mathcal M,g)$ be a compact connected smooth Riemannian manifold of dimension $d\ge1$, possibly with boundary, with Riemannian distance $d_g$. Let $C^\infty_{>0}(\mathcal M)$ be the set of smooth positive functions on $\mathcal M$ and
--   $$\mathcal D_{\mathrm{rigid}}=\{\rho\in C^\infty_{>0}(\mathcal M):\operatorname{Aut}(\mathcal M,d_g,\rho\,\mathrm{dVol}_g)=\{\mathrm{id}\}\}.$$
--   Then $\mathcal D_{\mathrm{rigid}}$ is open and dense in $C^\infty_{>0}(\mathcal M)$ with the Whitney $C^\infty$ topology:
--   1. if $\rho\in\mathcal D_{\mathrm{rigid}}$ and $\rho_n\in C^\infty_{>0}(\mathcal M)$ converge to $\rho$ in $C^\infty$, then $\rho_n\in\mathcal D_{\mathrm{rigid}}$ for all large $n$;
--   2. every $\rho\in C^\infty_{>0}(\mathcal M)$ is the $C^\infty$ limit of a sequence in $\mathcal D_{\mathrm{rigid}}$.
--
--   Symmetry breaking (C1) is thus the generic situation.
--
--   **Formalization Note** Openness and density are stated through sequences. This is equivalent to the topological statement because the Whitney $C^\infty$ topology on a compact manifold is metrisable (Definition A.23). $C^\infty$ convergence is written as uniform convergence of every derivative, in every chart, on every compact subset of the chart image. The paper also states the result with $\rho$ ranging over normalised densities; since $\mathcal D_{\mathrm{rigid}}$ is invariant under multiplication by positive constants, the two forms are equivalent.
-- source:
--   Syrota, Lopez i Serrano, Franck and Hauberg, Identifiable alignment of unpaired representations, arXiv:2611.11460v1 (2026), Section 3, Proposition 3.2, p. 5; appendix form Proposition B.8, Appendix B.2, pp. 23-26; Whitney topology Definition A.23, p. 20

import Mathlib
import Definitions.Def_IdentifiableAlignment_Basic

open MeasureTheory ProbabilityTheory Set Filter Topology Bundle
open scoped ENNReal ContDiff Manifold

namespace IdentifiableAlignment

theorem symmetry_breaking_generic {d : ℕ} [NeZero d] {M : Type*}
    [MetricSpace M] [ChartedSpace (EuclideanHalfSpace d) M] [IsManifold (𝓡∂ d) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓡∂ d) x)]
    [IsContMDiffRiemannianBundle (𝓡∂ d) ∞ (EuclideanSpace ℝ (Fin d)) (fun x : M => TangentSpace (𝓡∂ d) x)]
    [IsRiemannianManifold (𝓡∂ d) M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [ConnectedSpace M] :
    (∀ ρ ∈ rigidDensities d M, ∀ ρs : ℕ → M → ℝ, (∀ n, ρs n ∈ smoothPosDensities d M) →
      CinfTendsto d ρs ρ → ∀ᶠ n in atTop, ρs n ∈ rigidDensities d M) ∧
    (∀ ρ ∈ smoothPosDensities d M, ∃ ρs : ℕ → M → ℝ,
      (∀ n, ρs n ∈ rigidDensities d M) ∧ CinfTendsto d ρs ρ) := by sorry

end IdentifiableAlignment
