-- Prove2me | Theorems.Thm_GPHigherGauge_Flatness_tau_secondOrder
-- name    : GPHigherGauge.Flatness.tau_secondOrder
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:56:46.39006+00:00
-- url     : https://prove2.me/theorems/473909fa-0547-4bc8-b084-bf95ce072765
-- title:
--   Eq. (3.21) — $t(h_{\mu\nu})\sim e^{a^2\tau(B_{\mu\nu})}$, the second-order chain rule at zero velocity
-- statement:
--   Let $G,H$ be real Lie groups, $t:H\to G$ a smooth map with $t(1)=1$, and $\tau=dt_1:\mathfrak h\to\mathfrak g$. Let $c:\mathbb R\to H$ be smooth at $0$ with $c(0)=1$ and $c'(0)=0$. Then $t\circ c$ has velocity $0$ at $0$, and, writing $\varphi_1$ for the charts of $G$ and $H$ at the unit,
--   $$\frac{d^2}{da^2}\Big|_{a=0}\varphi_1\big(t(c(a))\big)=\tau\Big(\frac{d^2}{da^2}\Big|_{a=0}\varphi_1\big(c(a)\big)\Big).$$
--
--   Applied to $c(a)=h_{\mu\nu}(x,a)$, whose $a^2$-coefficient is $B_{\mu\nu}$, this says that the $a^2$-coefficient of $t(h_{\mu\nu})$ is $\tau(B_{\mu\nu})$: $\tau$ is the infinitesimal version of $t$.
--
--   Differences from the source:
--   - reading: t(h_μν) ∼ e^{a²τ(B_μν)} → for a curve c through 1 with zero velocity, t∘c has zero velocity and its second derivative at 0 is τ of that of c (charts at 1); reason: Mathlib has no Lie-group exponential; with B_μν = ½ c''(0) this is equality of the a² coefficients.
--   - generalization: t the homomorphism of a smooth crossed module → any smooth map t : H → G with t(1) = 1; reason: only smoothness and t(1) = 1 are used; the crossed module's t is an instance.
--   - generalization: the square label a ↦ h_μν(x, a) → any curve c smooth at 0 with c(0) = 1 and c'(0) = 0; reason: under (3.16) the square labels are such curves.
--   - generalization: finite-dimensional real Lie groups → Lie groups modelled on any real normed space; reason: the finite-dimensional groups of the paper are an instance.
-- source:
--   Girelli, Pfeiffer, Higher gauge theory — differential versus integral formulation, arXiv:hep-th/0309173v2, §3.3, Eq. (3.21), p. 16; §3.1, p. 14 (τ = dt)

import Mathlib
import Definitions.Def_GPHigherGauge_Flatness_tau

open scoped Manifold ContDiff

namespace GPHigherGauge.Flatness

/-- `t(h) ∼ e^{a²τ(B)}`: a smooth map `t` with `t 1 = 1` carries the `a²`-coefficient of a curve
of zero velocity at the unit to its image under `τ = dt`.

Girelli, Pfeiffer, *Higher gauge theory — differential versus integral formulation*,
arXiv:hep-th/0309173v2, §3.3, Eq. (3.21), p. 16:
"The map τ: 𝔥 → 𝔤 is the infinitesimal version of the map t: H → G, t(h_µν) ∼ e^{a²τ(B_µν)}."

Let `G`, `H` be Lie groups, `t : H → G` smooth with `t 1 = 1`, and `c : ℝ → H` smooth at `0` with
`c 0 = 1` and velocity `0` at `0`. Then `t ∘ c` has velocity `0` at `0`, and its second
derivative at `0` in the chart of `G` at `1` is `τ` of the second derivative of `c` in the chart
of `H` at `1`.

**Formalization Note** Reading 2: "∼ e^{a²τ(B)}" is read as equality of the second-order
coefficients, given that the first-order coefficient vanishes; with `c = h_μν(x, ·)` and the
coefficient `B_μν = ½ c''(0)` this is `t(h_μν)`'s coefficient `τ(B_μν)`. Only smoothness of `t`
and `t 1 = 1` are assumed. -/
theorem tau_secondOrder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) ∞ G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] [ChartedSpace F H] [Group H] [LieGroup 𝓘(ℝ, F) ∞ H]
    (t : H → G) (ht : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ t) (ht1 : t 1 = 1)
    (c : ℝ → H) (hc : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) ∞ c 0) (hc0 : c 0 = 1)
    (hc' : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) c 0 = 0) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun a => t (c a)) 0 = 0 ∧
      deriv (deriv (fun a => extChartAt 𝓘(ℝ, E) (1 : G) (t (c a)))) 0 =
        tau t (deriv (deriv (fun a => extChartAt 𝓘(ℝ, F) (1 : H) (c a))) 0) := by sorry

end GPHigherGauge.Flatness
