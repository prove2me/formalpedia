-- Prove2me | Theorems.Thm_LeakageSpectral_Shannon_Supplement_theorem_9
-- name    : LeakageSpectral.Shannon.Supplement.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:44:11.86421+00:00
-- url     : https://prove2.me/theorems/35e5603c-1a47-48f6-9cc4-2979f4f251a0
-- title:
--   Theorem 9, p. 17 — Euler multiplicity bound
-- statement:
--   Let $\mathbb G=\mathbb Z_m$ be a cyclic group with the discrete $\sigma$-algebra and $\tau$ a leakage channel (a Markov kernel from $\mathbb Z_m$ to a measurable space) with $I(S;L)>0$, used for every share; let $q$, $\mathcal W_\gamma$, $Q(\gamma)$ and $q_\gamma$ be as in Theorem 8, $\kappa_{d,\gamma}=\sum_{w\in\mathcal W_\gamma}q_\gamma(w)^{d+1}$ the within-class alignment, $\kappa_d=\sum_{w\ne0}q(w)^{d+1}$, and $\phi$ Euler's totient. For every $d\ge0$:
--
--   1. for every $\gamma\mid m$ with $Q(\gamma)>0$,
--   $$\kappa_{d,\gamma}=2^{-dH_{d+1}(q_\gamma)}\ge\phi(\gamma)^{-d};$$
--   2. $$\kappa_d\ge\sum_{\gamma\mid m}\frac{Q(\gamma)^{d+1}}{\phi(\gamma)^d};$$
--   3. if each $q_\gamma$ (with $Q(\gamma)>0$) is uniform on its order class, $q_\gamma(w)=1/\phi(\gamma)$, then both inequalities hold with equality.
--
--   The bound expresses how many Fourier modes of each order are available to spread, and thereby de-align, the leakage.
--
--   Differences from the source:
--
--   - encoding: a cyclic group ℤ_m (§5.1) → ZMod m with m ≠ 0 (NeZero m), discrete σ-algebra; reason: the same group
--   - encoding: 𝒲_γ = {w : ord χ_w = γ}, Q(γ) = Σ_{w∈𝒲_γ} q(w), q_γ = q/Q(γ) → OrderClass G γ (non-trivial characters with orderOf = γ in the character group), primitiveMass τ γ, condSpectrum τ γ; reason: the same objects; q_γ is used only where Q(γ) > 0
--   - reading: κ_{d,γ} = 2^{−dH_{d+1}(q_γ)} ≥ φ(γ)^{−d}, γ unrestricted → for every γ ∣ m with Q(γ) > 0; reason: q_γ is defined only for Q(γ) > 0 (Theorem 8)
--   - encoding: Σ_γ in κ_d ≥ Σ_γ Q(γ)^{d+1}/φ(γ)^d → sum over γ ∈ m.divisors; reason: every character order divides m; terms with Q(γ) = 0 vanish
--   - encoding: "the equality holds if the spectra are uniform among each primitive order class" → an implication from uniformity of every q_γ with Q(γ) > 0 to both equalities; reason: the source states only the sufficient direction
--   - reading: a channel without share index ("we may omit the subscript i, assuming that the leakages are i.i.d.", §2.1, p. 5) → one Markov kernel τ used for every share: globalJoint (fun _ => τ) d; reason: the paper's standing i.i.d. convention for unindexed statements
--   - encoding: standing assumption I(S;L) > 0 of §2.1, p. 5, not repeated in the theorem → hypothesis 0 < shannonMI (localJoint τ); reason: the standing assumption of the section, written as a binder as in the base mission
-- source:
--   Rei Ueno, A Spectral Theory of Local-to-Global Leakage, STOC 2027 submission #326 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/326.pdf, Theorem 9, Eq. (5), p. 17

import Mathlib
import Definitions.Def_LeakageSpectral_Shannon_Divergences
import Definitions.Def_LeakageSpectral_Shannon_JointLaw
import Definitions.Def_LeakageSpectral_Shannon_ShareModel
import Definitions.Def_LeakageSpectral_Shannon_Supplement_Defs
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LeakageSpectral.Shannon.Supplement

/-- Ueno, STOC 2027 submission #326, Theorem 9, p. 17: Euler multiplicity bound, for a cyclic group
`G = ℤ_m` and i.i.d. leakage through one channel `τ` with `I(S; L) > 0`. With
`κ_{d,γ} = ∑_{w ∈ 𝒲_γ} q_γ(w)^{d+1}`:
(i) `κ_{d,γ} = 2^{-d H_{d+1}(q_γ)} ≥ φ(γ)^{-d}` for every `γ ∣ m` with `Q(γ) > 0`;
(ii) `κ_d ≥ ∑_{γ ∣ m} Q(γ)^{d+1} / φ(γ)^d`;
(iii) if each `q_γ` is uniform on its order class, both inequalities are equalities. -/
theorem theorem_9 (m : ℕ) [NeZero m] {L : Type*} [MeasurableSpace L] (τ : Kernel (ZMod m) L)
    [IsMarkovKernel τ] (hdep : 0 < shannonMI (localJoint τ)) (d : ℕ) :
    (∀ γ ∈ m.divisors, 0 < primitiveMass τ γ →
        classAlignment τ γ d =
            (2 : ℝ) ^ (-(d : ℝ) * renyiEntropy ((d : ℝ) + 1) (condSpectrum τ γ)) ∧
          ((Nat.totient γ : ℝ) ^ d)⁻¹ ≤ classAlignment τ γ d) ∧
    ∑ γ ∈ m.divisors, primitiveMass τ γ ^ (d + 1) / (Nat.totient γ : ℝ) ^ d ≤
      spectralAlignment (fun _ : ℕ => τ) d ∧
    ((∀ γ ∈ m.divisors, 0 < primitiveMass τ γ →
        ∀ w : OrderClass (ZMod m) γ, condSpectrum τ γ w = 1 / (Nat.totient γ : ℝ)) →
      (∀ γ ∈ m.divisors, 0 < primitiveMass τ γ →
          classAlignment τ γ d = ((Nat.totient γ : ℝ) ^ d)⁻¹) ∧
        spectralAlignment (fun _ : ℕ => τ) d =
          ∑ γ ∈ m.divisors, primitiveMass τ γ ^ (d + 1) / (Nat.totient γ : ℝ) ^ d) := by sorry

end LeakageSpectral.Shannon.Supplement
