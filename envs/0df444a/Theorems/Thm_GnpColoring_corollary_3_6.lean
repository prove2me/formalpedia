-- Prove2me | Theorems.Thm_GnpColoring_corollary_3_6
-- name    : GnpColoring.corollary_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:36:03.983353+00:00
-- url     : https://prove2.me/theorems/e7254312-0b64-4699-8a9e-08d5c3b83672
-- title:
--   Corollary 3.6 — singleton terms of the Bochner identity
-- statement:
--   Let $G$ carry a valid block partition with singletons $S$, under the standing parameters of Section 3.1: $d>0$, $0<\eta<1/2$, $A>0$, $C>0$ and $\alpha=C\log d>1$. Let $\mu$ be uniform on proper $q$-colourings, $a=q-\bar\Delta$, $H_s=a_sL_s$ and $\nabla^c_\sigma f\in\mathbb R^S$ the recoloring gradient. For every $\kappa\in\mathbb R$ and every $f$,
--
--   $$\sum_{s\in S}\langle f,(a_s-\kappa q)H_sf\rangle+2\sum_{\{s,t\}\in E(G[S])}\langle H_sf,H_tf\rangle\ \ge\ \frac{a-\kappa q}{2}\sum_{c\in[q]}\mathbb E\big[\|\nabla^c_\sigma f\|_2^2\big]+\sum_{c\in[q]}\mathbb E\big[(\nabla^c_\sigma f)^\top A_{G[S]}\nabla^c_\sigma f\big].$$
--
--   This expresses the singleton part of $\langle f,B_\kappa f\rangle$ through recoloring gradients.
--
--   Differences from the source:
--   - encoding: standing hypotheses stated once in Sections 3.1–3.2 (valid partition, $0<\eta<1/2$, $A,C>0$, $\alpha>1$) → explicit hypotheses; reason: they are the section's assumptions; nothing is added
--   - encoding: $2\sum_{\{s,t\}\in E(G[S])}$ and $(\nabla)^\top A_{G[S]}\nabla$ → sums over ordered adjacent pairs $(s,t)\in S\times S$; reason: an unordered edge appears twice as an ordered pair
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Corollary 3.6, p.18

import Mathlib
import Definitions.Def_GnpColoring_accelSingle
import Definitions.Def_GnpColoring_recolorGrad
import Definitions.Def_GnpColoring_IsValidPartition
import Definitions.Def_GnpColoring_expect
import Definitions.Def_GnpColoring_alphaW
import Definitions.Def_GnpColoring_deltaBar
import Definitions.Def_mm_spectral

open scoped Classical
open Finset

namespace GnpColoring

/-- **Corollary 3.6 (singleton terms of the Bochner identity).** With `a := q − Δ̄`, for every `κ`
and every `f`,
`Σ_{s∈S} ⟨f, (a_s − κq) H_s f⟩ + 2 Σ_{{s,t}∈E(G[S])} ⟨H_s f, H_t f⟩
  ≥ ((a − κq)/2) Σ_{c∈[q]} E[‖∇^c_σ f‖²₂] + Σ_{c∈[q]} E[(∇^c_σ f)ᵀ A_{G[S]} (∇^c_σ f)]`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Corollary 3.6, p.18 (with the definitions of Section 3.3, p.17).

**Formalization Note** The setting is Section 3.2 (a valid block partition `S`) with the standing
parameters of Section 3.1. `(a_s − κq)H_s` is the pointwise product. `2Σ_{{s,t}∈E(G[S])}` is
written as the sum over ordered adjacent pairs `(s, t) ∈ S × S`, and the quadratic form of
`A_{G[S]}` likewise. `E` is the expectation under the uniform law `µ` on proper colourings;
`∇^c_σ f ∈ ℝ^S`. -/
theorem corollary_3_6 {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℕ) (d η A C D : ℝ)
    (S : Finset (Fin n)) (hd : 0 < d) (hη : 0 < η) (hη2 : η < 1 / 2) (hA : 0 < A) (hC : 0 < C)
    (hα : 1 < alphaW C d)
    (hS : IsValidPartition G d η A C D S) (κ : ℝ) (f : (Fin n → Fin q) → ℝ) :
    ((q : ℝ) - deltaBar d η - κ * q) / 2 *
        ∑ c : Fin q, expect (MarkovMixing.properColoringDist G q)
          (fun σ => ∑ s ∈ S, recolorGrad G f c σ s ^ 2) +
      ∑ c : Fin q, expect (MarkovMixing.properColoringDist G q)
          (fun σ => ∑ s ∈ S, ∑ t ∈ S,
            (if G.Adj s t then (1 : ℝ) else 0) * recolorGrad G f c σ s * recolorGrad G f c σ t) ≤
    ∑ s ∈ S, MarkovMixing.innerPi (MarkovMixing.properColoringDist G q) f
        (fun x => ((availCount G x s : ℝ) - κ * q) * accelSingle G q s f x) +
      ∑ s ∈ S, ∑ t ∈ S, (if G.Adj s t then
        MarkovMixing.innerPi (MarkovMixing.properColoringDist G q) (accelSingle G q s f) (accelSingle G q t f) else 0) := by sorry

end GnpColoring
