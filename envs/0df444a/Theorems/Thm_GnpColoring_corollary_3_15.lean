-- Prove2me | Theorems.Thm_GnpColoring_corollary_3_15
-- name    : GnpColoring.corollary_3_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:36:19.909951+00:00
-- url     : https://prove2.me/theorems/62ab978f-c85e-41bb-8fca-e3fb6239c4dc
-- title:
--   Corollary 3.15 — block terms via port gradients
-- statement:
--   Let $G$ carry a valid block partition with singletons $S$ and blocks $\mathcal B$, under the standing parameters of Section 3.1: $d>0$, $0<\eta<1/2$, $A>0$, $C>0$ and $\alpha=C\log d>1$. Let $\mu$ be uniform on proper $q$-colourings and $a=q-\bar\Delta$. Let $\lambda\ge1$ bound $\lambda_{\max}(\Lambda_{B,\tau})$ for every block $B$ and every feasible $\tau$, and assume $A\ge1$, $a\ge2$ and $1-\kappa\ge8\lambda\bar\Delta/a^2$. Then for every $f$,
--
--   $$q^2(1-\kappa)\sum_{B}\langle f,L_Bf\rangle+2q\sum_{B,\,s\in\partial B}\langle H_sf,L_Bf\rangle\ \ge\ \Big(\frac{a(1-\kappa)}{2\lambda}-\frac{4\bar\Delta}{a}\Big)\sum_B\sum_{c}\mathbb E\big[\|\tilde\nabla^c_{B,\sigma}f\|_2^2\big]+2\sum_B\sum_{s\in\partial B}\sum_c\mathbb E\big[\nabla^c_\sigma f(s)\,\tilde\nabla^c_{B,\sigma}f(\rho_{B,s})\big].$$
--
--   It is the block analogue of Corollary 3.6.
--
--   Differences from the source:
--   - encoding: standing hypotheses stated once in Sections 3.1–3.2 (valid partition, $0<\eta<1/2$, $A,C>0$, $\alpha>1$) → explicit hypotheses; reason: they are the section's assumptions; nothing is added
--   - encoding: $\lambda\ge\sup_{B,\tau}\lambda_{\max}(\Lambda_{B,\tau})$ → the variance inequality of `PortCovBound` for every block and every feasible $\tau$; reason: the quadratic form of $\Lambda_{B,\tau}$ is a variance; $\Lambda_{B,\tau}$ is defined only for feasible $\tau$
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Corollary 3.15, p.23

import Mathlib
import Definitions.Def_GnpColoring_accelSingle
import Definitions.Def_GnpColoring_blockLap
import Definitions.Def_GnpColoring_portGrad
import Definitions.Def_GnpColoring_recolorGrad
import Definitions.Def_GnpColoring_ports
import Definitions.Def_GnpColoring_portOf
import Definitions.Def_GnpColoring_extBoundary
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

/-- **Corollary 3.15 (block terms via port gradients).** Let `λ ≥ 1` bound `λ_max(Λ_{B,τ})` over all
blocks `B` and feasible `τ`. Assume `A ≥ 1`, `a = q − Δ̄ ≥ 2` and `1 − κ ≥ 8λΔ̄/a²`. Then for every `f`,
`q²(1 − κ) Σ_B ⟨f, L_B f⟩ + 2q Σ_{B, s∈∂B} ⟨H_s f, L_B f⟩
  ≥ (a(1 − κ)/(2λ) − 4Δ̄/a) Σ_B Σ_c E[‖∇̃^c_{B,σ} f‖²₂] + 2 Σ_B Σ_{s∈∂B} Σ_c E[∇^c_σ f(s) ∇̃^c_{B,σ} f(ρ_{B,s})]`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Corollary 3.15, p.23: "Let λ ≥ 1 be an upper bound for sup_{B,τ} λ_max(Λ_{B,τ}). Assume
A ≥ 1, a ≥ 2, and 1 − κ ≥ 8λΔ̄/a². Then, …"

**Formalization Note** Setting of Section 3.2 (valid partition `S`) with the standing parameters of
Section 3.1. `λ_max(Λ_{B,τ}) ≤ λ` is `PortCovBound` (variance form), for feasible `τ` (the
conditional law `ν_{B,τ}` exists only for those). `‖∇̃^c_{B,σ} f‖²₂` sums over the ports `P_B`;
`E` is under the uniform law `µ` on proper colourings. -/
theorem corollary_3_15 {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℕ) (d η A C D κ : ℝ)
    (S : Finset (Fin n)) (hd : 0 < d) (hη : 0 < η) (hη2 : η < 1 / 2) (hA : 0 < A) (hC : 0 < C)
    (hα : 1 < alphaW C d)
    (hS : IsValidPartition G d η A C D S) (lam : ℝ) (hlam1 : 1 ≤ lam)
    (hlam : ∀ B ∈ blocks G S, ∀ x : Fin n → Fin q, IsFeasible G q B x → PortCovBound G q B x lam)
    (hA1 : 1 ≤ A) (ha : 2 ≤ (q : ℝ) - deltaBar d η)
    (hκ : 8 * lam * deltaBar d η / ((q : ℝ) - deltaBar d η) ^ 2 ≤ 1 - κ) (f : (Fin n → Fin q) → ℝ) :
    (((q : ℝ) - deltaBar d η) * (1 - κ) / (2 * lam) - 4 * deltaBar d η / ((q : ℝ) - deltaBar d η)) *
        ∑ B ∈ blocks G S, ∑ c : Fin q, expect (MarkovMixing.properColoringDist G q)
          (fun σ => ∑ ρ ∈ ports G B, portGrad G q B f c σ ρ ^ 2) +
      2 * ∑ B ∈ blocks G S, ∑ s ∈ extBoundary G B, ∑ c : Fin q, expect (MarkovMixing.properColoringDist G q)
          (fun σ => recolorGrad G f c σ s * portGrad G q B f c σ (portOf G B s)) ≤
    (q : ℝ) ^ 2 * (1 - κ) * ∑ B ∈ blocks G S,
        MarkovMixing.innerPi (MarkovMixing.properColoringDist G q) f (blockLap (MarkovMixing.properColoringDist G q) B f) +
      2 * (q : ℝ) * ∑ B ∈ blocks G S, ∑ s ∈ extBoundary G B,
        MarkovMixing.innerPi (MarkovMixing.properColoringDist G q) (accelSingle G q s f) (blockLap (MarkovMixing.properColoringDist G q) B f) := by sorry

end GnpColoring
