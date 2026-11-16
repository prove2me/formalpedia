-- Prove2me | Theorems.Thm_LeakageSpectral_Shannon_Supplement_theorem_4
-- name    : LeakageSpectral.Shannon.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:40:17.928201+00:00
-- url     : https://prove2.me/theorems/cfb42174-7a99-4bff-b4de-43e70db859c7
-- title:
--   Theorem 4, p. 12 — exponential rate of the global $\chi^2$-MI
-- statement:
--   Let $\mathbb G$ be a finite abelian group with the discrete $\sigma$-algebra and $\tau$ a leakage channel (a Markov kernel from $\mathbb G$ to a measurable space) with $I(S;L)>0$, used for every share (i.i.d. leakage). Let $M=I_{\chi^2}(S;L)$ be the local $\chi^2$-mutual information, $q$ the normalized Fourier leakage spectrum and $H_\infty(q)=-\log_2\max_{w\ne0}q(w)$. For $Z=S_0+\dots+S_d$ with independent uniform shares and $X=(L_0,\dots,L_d)$, $L_i\sim\tau(S_i)$, the limit below exists and
--
--   $$-\lim_{d\to\infty}\frac1d\log_2 I_{\chi^2}(Z;X)=-\log_2 M+H_\infty(q).$$
--
--   The exponent of the global leakage thus has two parts: the noise part $-\log_2 M$ and an algebraic part $H_\infty(q)$ coming from the alignment of the Fourier spectrum across shares.
--
--   Differences from the source:
--
--   - reading: a channel without share index ("we may omit the subscript i, assuming that the leakages are i.i.d.", §2.1, p. 5) → one Markov kernel τ used for every share: globalJoint (fun _ => τ) d; reason: the paper's standing i.i.d. convention for unindexed statements
--   - encoding: standing assumption I(S;L) > 0 of §2.1, p. 5, not repeated in the theorem → hypothesis 0 < shannonMI (localJoint τ); reason: the standing assumption of the section, written as a binder as in the base mission
--   - encoding: the exponential rate −lim_{d→∞} (1/d) log(·) → Filter.Tendsto of −(1/d)·log₂(·) along atTop to the stated value; reason: the theorem asserts that the limit exists and equals that value; base-2 logarithms as in §2.1
-- source:
--   Rei Ueno, A Spectral Theory of Local-to-Global Leakage, STOC 2027 submission #326 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/326.pdf, Theorem 4, p. 12; proof pp. 12–13

import Mathlib
import Definitions.Def_LeakageSpectral_Shannon_Divergences
import Definitions.Def_LeakageSpectral_Shannon_JointLaw
import Definitions.Def_LeakageSpectral_Shannon_ShareModel
import Definitions.Def_LeakageSpectral_Shannon_Supplement_Defs
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LeakageSpectral.Shannon.Supplement

/-- Ueno, STOC 2027 submission #326, Theorem 4, p. 12 (proof pp. 12–13): exponential rate of the
global χ²-MI. For i.i.d. leakage through one channel `τ` with `I(S; L) > 0` and local χ²-MI
`M = I_χ²(S; L)`, the limit `lim_{d→∞} -(1/d) log₂ I_χ²(Z; X)` exists and equals `-log₂ M + H∞(q)`. -/
theorem theorem_4 {G : Type*} [AddCommGroup G] [Fintype G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G] {L : Type*} [MeasurableSpace L] (τ : Kernel G L) [IsMarkovKernel τ]
    (hdep : 0 < shannonMI (localJoint τ)) :
    Tendsto (fun d : ℕ => -(1 / (d : ℝ)) *
        Real.logb 2 (chiSquareMI (globalJoint (fun _ : ℕ => τ) d)))
      atTop (𝓝 (-Real.logb 2 (chiSquareMI (localJoint τ)) + minEntropy (spectrum τ))) := by sorry

end LeakageSpectral.Shannon.Supplement
