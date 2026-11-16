-- Prove2me | Theorems.Thm_LeakageSpectral_Shannon_Supplement_corollary_2
-- name    : LeakageSpectral.Shannon.Supplement.corollary_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:41:57.145689+00:00
-- url     : https://prove2.me/theorems/57d66849-0aa3-4273-8742-02801e8f9aa0
-- title:
--   Corollary 2, p. 13 — exponential rate of the global Shannon MI
-- statement:
--   Let $\mathbb G$ be a finite abelian group with the discrete $\sigma$-algebra and $\tau$ a leakage channel (a Markov kernel from $\mathbb G$ to a measurable space) with $I(S;L)>0$, used for every share (i.i.d. leakage), satisfying the strict weak worst-case condition
--   $$\rho^*=\max_{w\ne0}\operatorname*{ess\,sup}_l|\hat p_{S\mid L}(w\mid l)|<1.$$
--   Let $\alpha$ be the leakage sharpness of $\tau$ (Lemma 1), $q$ its normalized Fourier leakage spectrum and $H_\infty(q)=-\log_2\max_{w\ne0}q(w)$. For $Z=S_0+\dots+S_d$ and $X=(L_0,\dots,L_d)$, the limit below exists and
--   $$-\lim_{d\to\infty}\frac1d\log_2 I(Z;X)=-\log_2\bigl(\alpha I(S;L)\bigr)+H_\infty(q),$$
--   with $I$ the Shannon mutual information in bits.
--
--   It is the Shannon counterpart of Theorem 4 and gives the exponents compared in Theorem 6 and Theorem 7.
--
--   Differences from the source:
--
--   - reading: a channel without share index ("we may omit the subscript i, assuming that the leakages are i.i.d.", §2.1, p. 5) → one Markov kernel τ used for every share: globalJoint (fun _ => τ) d; reason: the paper's standing i.i.d. convention for unindexed statements
--   - encoding: standing assumption I(S;L) > 0 of §2.1, p. 5, not repeated in the theorem → hypothesis 0 < shannonMI (localJoint τ); reason: the standing assumption of the section, written as a binder as in the base mission
--   - encoding: the exponential rate −lim_{d→∞} (1/d) log(·) → Filter.Tendsto of −(1/d)·log₂(·) along atTop to the stated value; reason: the theorem asserts that the limit exists and equals that value; base-2 logarithms as in §2.1
--   - encoding: ρ* < 1 for the i.i.d. channel → rhoStar (fun _ => τ) < 1, the base ρ* of the constant family, valued in [0, ∞]; reason: the supremum over identical shares is the single-channel value
-- source:
--   Rei Ueno, A Spectral Theory of Local-to-Global Leakage, STOC 2027 submission #326 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/326.pdf, Corollary 2, p. 13

import Mathlib
import Definitions.Def_LeakageSpectral_Shannon_Divergences
import Definitions.Def_LeakageSpectral_Shannon_JointLaw
import Definitions.Def_LeakageSpectral_Shannon_ShareModel
import Definitions.Def_LeakageSpectral_Shannon_Supplement_Defs
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LeakageSpectral.Shannon.Supplement

/-- Ueno, STOC 2027 submission #326, Corollary 2, p. 13: exponential rate of the global Shannon MI.
For i.i.d. leakage through one channel `τ` with `I(S; L) > 0` satisfying the strict weak worst-case
condition `ρ* < 1`, the limit `lim_{d→∞} -(1/d) log₂ I(Z; X)` exists and equals
`-log₂ (α I(S; L)) + H∞(q)`, where `α` is the leakage sharpness of `τ`. -/
theorem corollary_2 {G : Type*} [AddCommGroup G] [Fintype G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G] {L : Type*} [MeasurableSpace L] (τ : Kernel G L) [IsMarkovKernel τ]
    (hdep : 0 < shannonMI (localJoint τ)) (hρ : rhoStar (fun _ : ℕ => τ) < 1) :
    Tendsto (fun d : ℕ => -(1 / (d : ℝ)) *
        Real.logb 2 (shannonMI (globalJoint (fun _ : ℕ => τ) d)))
      atTop (𝓝 (-Real.logb 2 (sharpness τ * shannonMI (localJoint τ)) +
        minEntropy (spectrum τ))) := by sorry

end LeakageSpectral.Shannon.Supplement
