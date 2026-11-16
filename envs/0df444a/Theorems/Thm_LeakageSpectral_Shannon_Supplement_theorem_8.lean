-- Prove2me | Theorems.Thm_LeakageSpectral_Shannon_Supplement_theorem_8
-- name    : LeakageSpectral.Shannon.Supplement.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:43:35.800146+00:00
-- url     : https://prove2.me/theorems/af9f8c54-8158-4919-9543-7464acf353a6
-- title:
--   Theorem 8, p. 16 — exact quotient alignment decomposition
-- statement:
--   Let $\mathbb G=\mathbb Z_m$ be a cyclic group with the discrete $\sigma$-algebra and $\tau$ a leakage channel (a Markov kernel from $\mathbb Z_m$ to a measurable space) with $I(S;L)>0$, used for every share (i.i.d. leakage); let $q$ be its normalized Fourier leakage spectrum on the non-trivial characters. For $\gamma\mid m$ let $\mathcal W_\gamma=\{w\ne0:\operatorname{ord}\chi_w=\gamma\}$, let $Q(\gamma)=\sum_{w\in\mathcal W_\gamma}q(w)$ be the **order-$\gamma$ primitive spectral mass**, and, when $Q(\gamma)>0$, let $q_\gamma(w)=q(w)/Q(\gamma)$ on $\mathcal W_\gamma$. Then for every $d\ge0$ the spectral alignment probability $\kappa_d=\sum_{w\ne0}q(w)^{d+1}$ satisfies
--
--   $$\kappa_d=\sum_{\gamma\mid m,\ Q(\gamma)>0}Q(\gamma)^{d+1}\sum_{w\in\mathcal W_\gamma}q_\gamma(w)^{d+1}=\sum_{\gamma\mid m,\ Q(\gamma)>0}2^{-dH_{d+1}(q_\gamma)}\,Q(\gamma)^{d+1},$$
--
--   with $H_{d+1}$ the Rényi entropy of order $d+1$ in bits ($H_1$ the Shannon entropy). The alignment thus splits into which quotient order leaks ($Q$) and how concentrated the leakage is inside each order class ($q_\gamma$).
--
--   Differences from the source:
--
--   - encoding: a cyclic group ℤ_m (§5.1) → ZMod m with m ≠ 0 (NeZero m), discrete σ-algebra; reason: the same group
--   - encoding: 𝒲_γ = {w : ord χ_w = γ}, Q(γ) = Σ_{w∈𝒲_γ} q(w), q_γ = q/Q(γ) → OrderClass G γ (non-trivial characters with orderOf = γ in the character group), primitiveMass τ γ, condSpectrum τ γ; reason: the same objects; q_γ is used only where Q(γ) > 0
--   - reading: sums over γ ∣ m, with q_γ defined only for Q(γ) > 0 → sums over γ ∣ m with Q(γ) > 0; reason: q_γ is undefined where Q(γ) = 0, and those terms carry the factor Q(γ)^{d+1} = 0
--   - reading: a channel without share index ("we may omit the subscript i, assuming that the leakages are i.i.d.", §2.1, p. 5) → one Markov kernel τ used for every share: globalJoint (fun _ => τ) d; reason: the paper's standing i.i.d. convention for unindexed statements
--   - encoding: standing assumption I(S;L) > 0 of §2.1, p. 5, not repeated in the theorem → hypothesis 0 < shannonMI (localJoint τ); reason: the standing assumption of the section, written as a binder as in the base mission
-- source:
--   Rei Ueno, A Spectral Theory of Local-to-Global Leakage, STOC 2027 submission #326 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/326.pdf, Theorem 8, p. 16; proof pp. 16–17

import Mathlib
import Definitions.Def_LeakageSpectral_Shannon_Divergences
import Definitions.Def_LeakageSpectral_Shannon_JointLaw
import Definitions.Def_LeakageSpectral_Shannon_ShareModel
import Definitions.Def_LeakageSpectral_Shannon_Supplement_Defs
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LeakageSpectral.Shannon.Supplement

/-- Ueno, STOC 2027 submission #326, Theorem 8, p. 16 (proof pp. 16–17): exact quotient alignment
decomposition, for a cyclic group `G = ℤ_m` and i.i.d. leakage through one channel `τ` with
`I(S; L) > 0`. With `Q(γ)` the order-`γ` primitive spectral mass and `q_γ = q / Q(γ)` on `𝒲_γ`,
`κ_d = ∑_{γ ∣ m, Q(γ) > 0} Q(γ)^{d+1} ∑_{w ∈ 𝒲_γ} q_γ(w)^{d+1}
     = ∑_{γ ∣ m, Q(γ) > 0} 2^{-d H_{d+1}(q_γ)} Q(γ)^{d+1}`. -/
theorem theorem_8 (m : ℕ) [NeZero m] {L : Type*} [MeasurableSpace L] (τ : Kernel (ZMod m) L)
    [IsMarkovKernel τ] (hdep : 0 < shannonMI (localJoint τ)) (d : ℕ) :
    spectralAlignment (fun _ : ℕ => τ) d =
        ∑ γ ∈ m.divisors with 0 < primitiveMass τ γ,
          primitiveMass τ γ ^ (d + 1) * ∑ w : OrderClass (ZMod m) γ, condSpectrum τ γ w ^ (d + 1) ∧
      spectralAlignment (fun _ : ℕ => τ) d =
        ∑ γ ∈ m.divisors with 0 < primitiveMass τ γ,
          (2 : ℝ) ^ (-(d : ℝ) * renyiEntropy ((d : ℝ) + 1) (condSpectrum τ γ)) *
            primitiveMass τ γ ^ (d + 1) := by sorry

end LeakageSpectral.Shannon.Supplement
