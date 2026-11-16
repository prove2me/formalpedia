-- Prove2me | Theorems.Thm_LeakageSpectral_Shannon_Supplement_eq_4
-- name    : LeakageSpectral.Shannon.Supplement.eq_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:39:50.850132+00:00
-- url     : https://prove2.me/theorems/2a87c172-1ed1-427a-bf84-e0cde2aa762c
-- title:
--   Equation (4), p. 12 — the alignment exponent is the min-entropy
-- statement:
--   Let $\mathbb G$ be a finite abelian group with the discrete $\sigma$-algebra and $\tau$ a leakage channel (a Markov kernel from $\mathbb G$ to a measurable space) with $I(S;L)>0$, used for every share (i.i.d. leakage). Let $q$ be its normalized Fourier leakage spectrum on the non-trivial characters and
--   $$\kappa_d=\Pr[W_0=\dots=W_d]=\sum_{w\ne0}q(w)^{d+1},\qquad W_i\stackrel{\text{iid}}{\sim}q,$$
--   the spectral alignment probability. Then the limit below exists and
--   $$-\lim_{d\to\infty}\frac1d\log_2\kappa_d=-\log_2\|q\|_\infty=H_\infty(q),$$
--   where $\|q\|_\infty=\max_{w\neq0}|q(w)|$ and $H_\infty(q)=-\log_2\max_w q(w)$ is the min-entropy in bits.
--
--   It is the first step of the proof of Theorem 4: the largest spectral component alone determines the exponent of $\kappa_d$.
--
--   Differences from the source:
--
--   - reading: a channel without share index ("we may omit the subscript i, assuming that the leakages are i.i.d.", §2.1, p. 5) → one Markov kernel τ used for every share: globalJoint (fun _ => τ) d; reason: the paper's standing i.i.d. convention for unindexed statements
--   - encoding: standing assumption I(S;L) > 0 of §2.1, p. 5, not repeated in the theorem → hypothesis 0 < shannonMI (localJoint τ); reason: the standing assumption of the section, written as a binder as in the base mission
--   - encoding: the exponential rate −lim_{d→∞} (1/d) log(·) → Filter.Tendsto of −(1/d)·log₂(·) along atTop to the stated value; reason: the theorem asserts that the limit exists and equals that value; base-2 logarithms as in §2.1
--   - encoding: ‖q‖∞ and H∞(q) → ⨆ w, |spectrum τ w| and minEntropy q = −log₂ ⨆ w, q w over the finite set of non-trivial characters; reason: the maximum of finitely many values; the set is nonempty under I(S;L) > 0
-- source:
--   Rei Ueno, A Spectral Theory of Local-to-Global Leakage, STOC 2027 submission #326 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/326.pdf, Equation (4), p. 12 (proof of Theorem 4)

import Mathlib
import Definitions.Def_LeakageSpectral_Shannon_Divergences
import Definitions.Def_LeakageSpectral_Shannon_JointLaw
import Definitions.Def_LeakageSpectral_Shannon_ShareModel
import Definitions.Def_LeakageSpectral_Shannon_Supplement_Defs
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LeakageSpectral.Shannon.Supplement

/-- Ueno, STOC 2027 submission #326, Equation (4), p. 12 (proof of Theorem 4): for i.i.d. leakage
through one channel `τ` with `I(S; L) > 0`, the spectral alignment probability
`κ_d = ∑_{w ≠ 0} q(w)^{d+1}` satisfies `lim_{d→∞} -(1/d) log₂ κ_d = -log₂ ‖q‖∞ = H∞(q)`. -/
theorem eq_4 {G : Type*} [AddCommGroup G] [Fintype G] [MeasurableSpace G] [DiscreteMeasurableSpace G]
    {L : Type*} [MeasurableSpace L] (τ : Kernel G L) [IsMarkovKernel τ]
    (hdep : 0 < shannonMI (localJoint τ)) :
    Tendsto (fun d : ℕ => -(1 / (d : ℝ)) * Real.logb 2 (spectralAlignment (fun _ : ℕ => τ) d))
        atTop (𝓝 (minEntropy (spectrum τ))) ∧
      minEntropy (spectrum τ) = -Real.logb 2 (⨆ w, |spectrum τ w|) := by sorry

end LeakageSpectral.Shannon.Supplement
