-- Prove2me | Theorems.Thm_LeakageSpectral_Shannon_eq_16
-- name    : LeakageSpectral.Shannon.eq_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:29.229664+00:00
-- url     : https://prove2.me/theorems/4eb38ea3-c17c-4e57-b1e9-33d71d4fcd3c
-- title:
--   Eq. (16), p. 29 — uniform convergence of the global posterior
-- statement:
--   In the setting of additive sharing with independent uniform shares, let $I(S_i;L_i)>0$ for all $i$ and let $\rho^*<1$. Then for every $d$ and almost every $x$, for all $z\in\mathbb G$,
--
--   $$
--   \Big|\frac{p_{Z\mid X}(z\mid x)}{p_Z(z)}-1\Big|\le\sum_{w\neq0}|\hat p_{Z\mid X}(w\mid x)|\le(m-1)(\rho^*)^{d+1},
--   $$
--
--   and the bound $(m-1)(\rho^*)^{d+1}$ tends to $0$ as $d\to\infty$. So the global likelihood ratio converges uniformly to $1$, at an exponential rate.
--
--   Differences from the source:
--   - encoding: the posterior $p_{Z\mid X}(z\mid x)$ → $p_Z(z)\,r(z,x)$, with $r$ the real value of the Radon–Nikodym derivative of the joint law of $(Z,X)$ against the product of its marginals; reason: the source says so on p. 29 ("precisely, $r$ is defined as the Radon–Nikodym derivative in Equation (2)")
--   - encoding: the posterior $p_{S\mid L}(s\mid l)$ of the leakage model → $p_S(s)\,r(s,l)$, with $r$ the real value of the Radon–Nikodym derivative of Eq. (2), of the joint law against the product of its marginals; reason: the source states this relation itself on p. 9 ($r=p_{S\mid L=l}/p_S$); it is the posterior for a general leakage space, and it is determined for almost every $l$
--   - encoding: frequencies $w\in\mathcal W$ with characters $\chi_w$, and $w\neq0$ → `AddChar G ℂ` and its non-trivial elements (`NontrivialChar G`); reason: the same objects: the character group of $\mathbb G$, indexed directly rather than through $\mathcal W$
--   - reading: $Z=S_0+\dots+S_d$, with §1.1 opening "Let $Z$ be a random variable" → the shares are independent and uniform on $G$, each $L_i$ depends on $S_i$ alone, and $Z$ is their sum, hence uniform; reason: the proofs use "the independence assumption" (p. 27) and a uniform $p_Z$; with an arbitrary $Z$ the statements fail: $G=\mathbb Z_2$, $Z\equiv0$, $S_1=S_0$ uniform, channel $(1+l(-1)^s/2)/2$ on $l=\pm1$ has $I(Z;X)=0$ and a positive right-hand side
--   - encoding: random variables $(Z,X)$ on an unnamed probability space → the explicit joint law $m^{-(d+1)}\sum_s\delta_{s_0+\dots+s_d}\otimes\bigotimes_i\tau_i(s_i)$; reason: every quantity depends only on this law, and this sum is that law
--   - encoding: Shannon mutual information $I(\cdot;\cdot)$ in bits → `(klDiv P (P.fst.prod P.snd)).toReal / Real.log 2`; reason: Mathlib's `klDiv` is in nats and valued in $[0,\infty]$; here it is finite because the first coordinate is finite
--   - encoding: $\rho^*$ as a real number → `rhoStar τ`, valued in $[0,\infty]$, with its real value where a power is taken; reason: the supremum in $[0,\infty]$ has no junk value; below $1$ it is the same number
--   - encoding: $\|\cdot\|_\infty\le(m-1)(\rho^*)^{d+1}=o(1)$ → the bound for all $z$ and almost every $x$, and a `Tendsto` clause for the bound; reason: an essential supremum bound is exactly an almost-everywhere bound; $o(1)$ is the limit
--   - encoding: shares of a fixed $d$, with $\rho^*$ a supremum over $i$ → channels `τ : ∀ i : ℕ, Kernel G (L i)`, with the first `d + 1` used at each $d$; reason: the source's asymptotics in $d$ fix one sequence of channels, as Theorem 2 does
-- source:
--   Rei Ueno, A Spectral Theory of Local-to-Global Leakage, STOC 2027 submission #326 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/326.pdf, Appendix B.3 display and Eq. (16), p. 29

import Mathlib
import Definitions.Def_LeakageSpectral_Shannon_Divergences
import Definitions.Def_LeakageSpectral_Shannon_JointLaw
import Definitions.Def_LeakageSpectral_Shannon_ShareModel
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LeakageSpectral.Shannon

/-- Eq. (16) and the display before it, p. 29: for all `z` and almost every `x`,
`|p_{Z∣X}(z ∣ x)/p_Z(z) - 1| ≤ ∑_{w ≠ 0} |p̂_{Z∣X}(w ∣ x)| ≤ (m - 1)(ρ*)^{d+1}`, and the bound is `o(1)`
as `d → ∞`. -/
theorem eq_16 {G : Type*} [AddCommGroup G] [Fintype G] [MeasurableSpace G] [DiscreteMeasurableSpace G]
    {L : ℕ → Type*} [∀ i, MeasurableSpace (L i)] (τ : ∀ i, Kernel G (L i)) [∀ i, IsMarkovKernel (τ i)]
    (hdep : ∀ i, 0 < shannonMI (localJoint (τ i))) (hρ : rhoStar τ < 1) :
    (∀ d : ℕ, ∀ᵐ x ∂(globalJoint τ d).snd, ∀ z : G,
        |posterior (globalJoint τ d) z x / firstMarginal (globalJoint τ d) z - 1| ≤
            ∑ w : NontrivialChar G, ‖posteriorDFT (globalJoint τ d) w.1 x‖ ∧
          ∑ w : NontrivialChar G, ‖posteriorDFT (globalJoint τ d) w.1 x‖ ≤
            ((Fintype.card G : ℝ) - 1) * (rhoStar τ).toReal ^ (d + 1)) ∧
      Filter.Tendsto (fun d : ℕ => ((Fintype.card G : ℝ) - 1) * (rhoStar τ).toReal ^ (d + 1))
        Filter.atTop (nhds 0) := by sorry

end LeakageSpectral.Shannon
