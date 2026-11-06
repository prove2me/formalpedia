-- Prove2me | Theorems.Thm_GnpColoring_theorem_1_1
-- name    : GnpColoring.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:31:56.349928+00:00
-- url     : https://prove2.me/theorems/0d268436-4bc2-41c6-9264-19d24ed1b7c5
-- title:
--   Theorem 1.1 — Glauber dynamics mixes in $O_{d,\varepsilon}(n^{2+C_\varepsilon\log q/d^\varepsilon}(1+\log(1/\delta)))$ steps for $q\ge d+d^{1/2+\varepsilon}$
-- statement:
--   For every $0<\varepsilon\le1/2$ there is a constant $C_\varepsilon>0$, depending only on $\varepsilon$, such that for all sufficiently large $d$ there is $K>0$ (depending on $d$ and $\varepsilon$) such that for every integer $q\ge d+d^{\varepsilon}\sqrt d$ the following holds with probability $1-o(1)$ as $n\to\infty$ over $G\sim G(n,d/n)$: $G$ has a proper $q$-colouring and, for every $0<\delta<1$, the mixing time of Glauber dynamics for proper $q$-colourings of $G$,
--
--   $$\tau_{\mathrm{mix}}(\delta)=\max_\sigma\min\{t\in\mathbb Z_{\ge0}:D_{\mathrm{TV}}(P^t_{\mathrm{GD}}(\sigma,\cdot),\mu_{q,G})\le\delta\},$$
--
--   satisfies
--
--   $$\tau_{\mathrm{mix}}(\delta)\le K\,n^{2+\zeta}\big(1+\log(1/\delta)\big),\qquad\zeta=\frac{C_\varepsilon\log q}{d^\varepsilon}.$$
--
--   Glauber dynamics picks a uniform vertex and recolours it uniformly among the colours absent from its neighbourhood; $\mu_{q,G}$ is the uniform measure on proper colourings. The result gives almost quadratic mixing with only $d+d^{1/2+\varepsilon}$ colours on sparse random graphs.
--
--   Differences from the source:
--   - encoding: $G\sim G(n,d/n)$, "with probability $1-o(1)$" → probability under the Erdős–Rényi law with edge probability $d/n$ clamped into $[0,1]$ tends to $1$ as $n\to\infty$; reason: the clamp only affects $n<d$, which the limit never sees
--   - encoding: vertices $[n]$, colours $[q]$ → `Fin n`, `Fin q`; reason: 0-based relabelling
--   - reading: $\mu_{q,G}$ "whenever it is nonempty"; the bound on $\tau_{\mathrm{mix}}$ → the event includes that a proper $q$-colouring exists; reason: otherwise $\tau_{\mathrm{mix}}$ is undefined and a graph without proper colourings would satisfy the bound vacuously
--   - encoding: $\tau_{\mathrm{mix}}(\delta)=O_{d,\varepsilon}(n^{2+\zeta}(1+\log(1/\delta)))$ → $\exists K>0$ after $d$, before $q$, with $d(t)\le\delta$ for every integer $t\ge Kn^{2+\zeta}(1+\log(1/\delta))$; reason: $O_{d,\varepsilon}$ names $d,\varepsilon$ only; $t\mapsto D_{\mathrm{TV}}(P^t(\sigma,\cdot),\mu)$ is nonincreasing, so this is $\tau_{\mathrm{mix}}(\delta)\le Kn^{2+\zeta}(1+\log(1/\delta))$
--   - encoding: $D_{\mathrm{TV}}=\frac12\sum|\nu-\mu|$ → `MarkovMixing.tvDist` (maximum over events); reason: equal for probability vectors
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Theorem 1.1, p.4

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_mm_transport
import Definitions.Def_mm_mixing
import Definitions.Def_mm_basic

open scoped Classical
open Finset
open Filter Topology

namespace GnpColoring

/-- **Theorem 1.1 (main theorem).** For all `0 < ε ≤ 1/2` there is `C_ε > 0` such that for all
sufficiently large `d` there is `K` (= the constant of `O_{d,ε}`) such that for all integers
`q ≥ d + d^ε √d`: with probability `1 − o(1)` over `G ∼ G(n, d/n)`, `G` has a proper `q`-colouring and,
for every `0 < δ < 1`, the mixing time of Glauber dynamics for proper `q`-colourings satisfies
`τ_mix(δ) ≤ K n^(2+ζ) (1 + log(1/δ))` with `ζ = C_ε log(q)/d^ε`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Theorem 1.1, p.4: "The following holds for all 0 < ε ≤ 1/2, sufficiently large d, and all
integers q ≥ d + d^ε√d. With probability 1 − o(1) over the draw of G ∼ G(n, d/n), for every
0 < δ < 1, the mixing time τ_mix(δ) := max_σ min{t ∈ ℤ≥0 | D_TV(P^t_GD(σ, ·), µ_{q,G}) ≤ δ} of
Glauber dynamics for proper q-colorings on G satisfies τ_mix(δ) = O_{d,ε}(n^(2+ζ)(1 + log(1/δ))) with
ζ := C_ε log(q)/d^ε, where C_ε > 0 is a constant that only depends on ε."

**Formalization Note**
* `G(n, d/n)` is `LPCommunity.SBMRecovery.erProb n (d/n)` (vertices `Fin n`; the edge probability is
  clamped into `[0, 1]`, which only matters for `n < d`); "with probability `1 − o(1)`" is
  convergence of the probability to `1` as `n → ∞` with `ε, C_ε, d, K, q` fixed first.
* `µ_{q,G}` is defined only when proper colourings exist (p.13: "whenever it is nonempty"); the
  event therefore includes `Ω_{q,G} ≠ ∅`. Without it a graph with no proper colouring would satisfy
  the bound vacuously.
* `τ_mix(δ) ≤ X` is written as `d(t) ≤ δ` for every integer `t ≥ X`, with
  `d(t) = max_σ D_TV(P^t(σ,·), µ)` (`MarkovMixing.distStationary`); this is equivalent because
  `t ↦ D_TV(P^t(σ,·), µ)` is nonincreasing for a chain with stationary law `µ`. `D_TV` is
  `MarkovMixing.tvDist` (supremum over events, equal to half the `ℓ¹` distance).
* Glauber dynamics is `MarkovMixing.coloringGlauber G q` (uniform vertex, heat-bath resampling
  among the available colours) on the subtype of proper colourings; `µ_{q,G}` is the uniform law
  there. `d^ε√d = d^(1/2+ε)`. `log` is natural. -/
theorem theorem_1_1 :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
    ∃ Cε : ℝ, 0 < Cε ∧ ∃ d₀ : ℝ, ∀ d : ℝ, d₀ ≤ d →
    ∃ K : ℝ, 0 < K ∧ ∀ q : ℕ, d + d ^ ((1 : ℝ) / 2 + ε) ≤ (q : ℝ) →
      Tendsto (fun n : ℕ => LPCommunity.SBMRecovery.erProb n (d / n) (fun G =>
          Nonempty {σ : Fin n → Fin q // MarkovMixing.IsProperColoring G σ} ∧
          ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ t : ℕ,
            K * (n : ℝ) ^ (2 + Cε * Real.log q / d ^ ε) * (1 + Real.log (1 / δ)) ≤ (t : ℝ) →
            MarkovMixing.distStationary (MarkovMixing.coloringGlauber G q)
              (MarkovMixing.uniformDist _) t ≤ δ))
        atTop (𝓝 1) := by sorry

end GnpColoring
