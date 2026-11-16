-- Prove2me | Theorems.Thm_LeakageSpectral_Shannon_Supplement_theorem_6
-- name    : LeakageSpectral.Shannon.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:42:20.420821+00:00
-- url     : https://prove2.me/theorems/c163f0ed-112a-467f-ad30-6ac0a6208b9c
-- title:
--   Theorem 6, p. 14 — universal separation of permutation-invariant local leakage magnitudes
-- statement:
--   A **local leakage magnitude** is a quantity $J$ computed from a leakage channel $\tau$ (the law of $(S,L)$ with $S$ uniform); it is **permutation-invariant** if $J(\tau\circ\pi)=J(\tau)$ for every channel $\tau$ and every permutation $\pi$ of $\mathbb G$, where $(\tau\circ\pi)(s)=\tau(\pi(s))$. Examples are the $\chi^2$-MI, the Shannon MI and the $L_\theta$- and $L_\theta^\psi$-MI.
--
--   For every $l\ge2$ and $\mathbb G=\mathbb Z_{2^l}$ (discrete $\sigma$-algebra) there are full-support binary leakage channels $\tau,\tau'$, both with $I(S;L)>0$ and both satisfying the strict weak worst-case condition $\rho^*<1$, such that
--
--   1. every permutation-invariant local leakage magnitude $J$, with values in any type, takes the same value on $\tau$ and $\tau'$;
--   2. $H_\infty(q^\tau)-H_\infty(q^{\tau'})>0$, where $q^\tau$ is the normalized Fourier leakage spectrum of $\tau$ and $H_\infty$ the min-entropy in bits;
--   3. for i.i.d. leakage and $Z=S_0+\dots+S_d$, the limit below exists and
--   $$-\lim_{d\to\infty}\frac1d\log_2\frac{I(Z;X^\tau)}{I(Z;X^{\tau'})}=H_\infty(q^\tau)-H_\infty(q^{\tau'}).$$
--
--   So no permutation-invariant local magnitude determines the exponent of the global Shannon leakage.
--
--   Differences from the source:
--
--   - generalization: "For some 𝔾, pairs … exist" → for every l ≥ 2, with G = ZMod (2^l); reason: the proof constructs the pair on ℤ_{2^l}, l ≥ 2; any one such l gives the printed existential
--   - generalization: "Let J(S;L) be a permutation-invariant local leakage magnitude … J(S;L^τ) = J(S;L^τ′)" → one pair (τ, τ′) on which every permutation-invariant J : Kernel G Bool → β, for every type β, agrees; reason: the proof's pair is related by an input permutation and works for all J at once; specializing to the given J gives the printed statement
--   - encoding: permutation-invariant magnitude J(S;L) → J a function of the channel with J (τ₀.comap π) = J τ₀ for all kernels τ₀ and all π : Equiv.Perm G; reason: with S uniform the joint law of (S,L) and the kernel determine each other, and relabelling S by π is τ ↦ τ ∘ π, the property the proof uses
--   - reading: "pairs of (full-support) leakage channels … it can hold" → ∃ full-support Markov kernels τ τ′ : Kernel (ZMod (2^l)) Bool, each with I(S;L) > 0 and ρ* < 1; reason: binary leakage, I(S;L) > 0 and ρ* < 1 are properties of the proof's channels (via Theorem 3) under which the Shannon exponent of Corollary 2 exists
--   - encoding: −lim (1/d) log ratio = H∞(q^τ) − H∞(q^τ′) > 0 → the value is positive (clause 2) and the Tendsto of −(1/d)·log₂(ratio) to it (clause 3); reason: the same claim; the limit exists
--   - reading: a channel without share index ("we may omit the subscript i, assuming that the leakages are i.i.d.", §2.1, p. 5) → one Markov kernel τ used for every share: globalJoint (fun _ => τ) d; reason: the paper's standing i.i.d. convention for unindexed statements
-- source:
--   Rei Ueno, A Spectral Theory of Local-to-Global Leakage, STOC 2027 submission #326 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/326.pdf, Theorem 6, p. 14 (proof p. 14)

import Mathlib
import Definitions.Def_LeakageSpectral_Shannon_Divergences
import Definitions.Def_LeakageSpectral_Shannon_JointLaw
import Definitions.Def_LeakageSpectral_Shannon_ShareModel
import Definitions.Def_LeakageSpectral_Shannon_Supplement_Defs
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LeakageSpectral.Shannon.Supplement

/-- Ueno, STOC 2027 submission #326, Theorem 6, p. 14: universal separation of permutation-invariant
local leakage magnitudes. For every `l ≥ 2` and `G = ℤ_{2^l}` there are full-support binary channels
`τ`, `τ'`, both with `I(S; L) > 0` and `ρ* < 1`, such that every permutation-invariant local leakage
magnitude `J` (any function of the channel unchanged by input permutations, with any codomain) takes
the same value on both, while
`lim_{d→∞} -(1/d) log₂ (I(Z; X^τ) / I(Z; X^τ')) = H∞(q^τ) - H∞(q^τ') > 0`. -/
theorem theorem_6 (l : ℕ) (hl : 2 ≤ l) :
    ∃ τ τ' : Kernel (ZMod (2 ^ l)) Bool, IsMarkovKernel τ ∧ IsMarkovKernel τ' ∧
      FullSupport τ ∧ FullSupport τ' ∧
      0 < shannonMI (localJoint τ) ∧ 0 < shannonMI (localJoint τ') ∧
      rhoStar (fun _ : ℕ => τ) < 1 ∧ rhoStar (fun _ : ℕ => τ') < 1 ∧
      (∀ (β : Type*) (J : Kernel (ZMod (2 ^ l)) Bool → β), IsPermInvariant J → J τ = J τ') ∧
      0 < minEntropy (spectrum τ) - minEntropy (spectrum τ') ∧
      Tendsto (fun d : ℕ => -(1 / (d : ℝ)) *
          Real.logb 2 (shannonMI (globalJoint (fun _ : ℕ => τ) d) /
            shannonMI (globalJoint (fun _ : ℕ => τ') d)))
        atTop (𝓝 (minEntropy (spectrum τ) - minEntropy (spectrum τ'))) := by sorry

end LeakageSpectral.Shannon.Supplement
