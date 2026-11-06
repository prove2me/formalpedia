-- Prove2me | Theorems.Thm_GnpColoring_corollary_3_26
-- name    : GnpColoring.corollary_3_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:36:17.721966+00:00
-- url     : https://prove2.me/theorems/10586e8c-c9b6-43d5-8247-40aa8c290c28
-- title:
--   Corollary 3.26 — the assembled Bochner inequality
-- statement:
--   Under the assumptions of Corollary 3.15, for every $f$,
--
--   $$\langle f,B_\kappa f\rangle\ \ge\ \min\Big\{\frac{a-\kappa q}{2},\ \frac{a(1-\kappa)}{2\lambda}-\frac{4\bar\Delta}{a}\Big\}\sum_{c\in[q]}\mathbb E\big[\|\hat\nabla^c_\sigma f\|_2^2\big]+\sum_{c\in[q]}\mathbb E\big[(\hat\nabla^c_\sigma f)^\top A_\partial\,\hat\nabla^c_\sigma f\big],$$
--
--   where $B_\kappa=\tilde L^2-\kappa q\tilde L$, $A_\partial$ is the adjacency matrix of the graph of edges of $G$ with an endpoint in $S$, and $\hat\nabla^c_\sigma f\in\mathbb R^V$ is the combined gradient (recoloring gradient at singletons, port gradient at ports, $0$ elsewhere).
--
--   Together with a lower bound on the smallest eigenvalue of $A_\partial$ (Lemma 3.27) this shows $B_\kappa\succeq0$.
--
--   Differences from the source:
--   - encoding: standing hypotheses stated once in Sections 3.1–3.2 (valid partition, $0<\eta<1/2$, $A,C>0$, $\alpha>1$) → explicit hypotheses; reason: they are the section's assumptions; nothing is added
--   - encoding: $\lambda\ge\sup_{B,\tau}\lambda_{\max}(\Lambda_{B,\tau})$ → `PortCovBound` for every block and every feasible $\tau$; reason: as in Corollary 3.15
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Corollary 3.26, p.33

import Mathlib
import Definitions.Def_GnpColoring_bochnerOp
import Definitions.Def_GnpColoring_combinedGrad
import Definitions.Def_GnpColoring_boundaryAdj
import Definitions.Def_GnpColoring_blocks
import Definitions.Def_GnpColoring_IsValidPartition
import Definitions.Def_GnpColoring_IsFeasible
import Definitions.Def_GnpColoring_PortCovBound
import Definitions.Def_GnpColoring_expect
import Definitions.Def_GnpColoring_alphaW
import Definitions.Def_GnpColoring_deltaBar
import Definitions.Def_mm_spectral

open scoped Classical
open Finset

namespace GnpColoring

/-- **Corollary 3.26 (assembled Bochner inequality).** Under the assumptions of Corollary 3.15, for
every `f`,
`⟨f, B_κ f⟩ ≥ min{(a − κq)/2, a(1 − κ)/(2λ) − 4Δ̄/a} Σ_c E[‖∇̂^c_σ f‖²₂] + Σ_c E[(∇̂^c_σ f)ᵀ A_∂ (∇̂^c_σ f)]`,
where `A_∂` is the adjacency matrix of `G_∂` (the edges of `G` with an endpoint in `S`) and
`∇̂^c_σ f ∈ ℝ^V` is the combined gradient.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Corollary 3.26, p.33: "Under the assumptions of Corollary 3.15, we have …, where λ is the
covariance upper bound from Corollary 3.15."

**Formalization Note** Same hypotheses as `corollary_3_15`. `B_κ = L̃² − κqL̃` (p.16); the
quadratic form of `A_∂` is `Σ_u Σ_v (A_∂)_{uv} z_u z_v`. -/
theorem corollary_3_26 {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℕ) (d η A C D κ : ℝ)
    (S : Finset (Fin n)) (hd : 0 < d) (hη : 0 < η) (hη2 : η < 1 / 2) (hA : 0 < A) (hC : 0 < C)
    (hα : 1 < alphaW C d)
    (hS : IsValidPartition G d η A C D S) (lam : ℝ) (hlam1 : 1 ≤ lam)
    (hlam : ∀ B ∈ blocks G S, ∀ x : Fin n → Fin q, IsFeasible G q B x → PortCovBound G q B x lam)
    (hA1 : 1 ≤ A) (ha : 2 ≤ (q : ℝ) - deltaBar d η)
    (hκ : 8 * lam * deltaBar d η / ((q : ℝ) - deltaBar d η) ^ 2 ≤ 1 - κ) (f : (Fin n → Fin q) → ℝ) :
    min (((q : ℝ) - deltaBar d η - κ * q) / 2)
        (((q : ℝ) - deltaBar d η) * (1 - κ) / (2 * lam) -
          4 * deltaBar d η / ((q : ℝ) - deltaBar d η)) *
        ∑ c : Fin q, expect (MarkovMixing.properColoringDist G q) (fun σ => ∑ v, combinedGrad G q S f c σ v ^ 2) +
      ∑ c : Fin q, expect (MarkovMixing.properColoringDist G q)
        (fun σ => ∑ u, ∑ v, boundaryAdj G S u v * combinedGrad G q S f c σ u *
          combinedGrad G q S f c σ v) ≤
    MarkovMixing.innerPi (MarkovMixing.properColoringDist G q) f (bochnerOp G q S κ f) := by sorry

end GnpColoring
