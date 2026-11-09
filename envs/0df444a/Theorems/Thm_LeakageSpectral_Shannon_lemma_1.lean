-- Prove2me | Theorems.Thm_LeakageSpectral_Shannon_lemma_1
-- name    : LeakageSpectral.Shannon.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:15.661485+00:00
-- url     : https://prove2.me/theorems/3d1d25d0-4c20-4b1e-aaf5-8a5ea69f87d3
-- title:
--   Lemma 1, p. 9 — conversion between Shannon MI and $\chi^2$-MI
-- statement:
--   Let $S$ be uniform on the finite abelian group $\mathbb G$, let $L$ be drawn from a Markov kernel $\tau$ given $S$, with values in any measurable space, and assume $I(S;L)>0$. Let $r$ be the likelihood ratio of Eq. (2), let $f(r)=r\ln r-r+1$ and $g(r)=(r-1)^2/f(r)$ with $g(1):=2$, and let
--
--   $$
--   \mu(s,\mathrm dl)=\frac{f(r(s,l))}{\ln(2)\,I(S;L)}\,p_S(s)\,p_L(\mathrm dl).
--   $$
--
--   Then:
--
--   1. $\mu$ is a probability measure;
--   2. for each $s$ and $p_L$-almost every $l$, $r(s,l)=\dfrac{\mathrm dp_{L\mid S=s}}{\mathrm dp_L}(l)$;
--   3. with $\alpha=\ln(2)\,\mathbb E_\mu\,g(r)$,
--
--   $$
--   I_{\chi^2}(S;L)=\alpha\,I(S;L).
--   $$
--
--   The factor $\alpha$ is the leakage sharpness: it measures how much more weight the $\chi^2$-MI gives to rare, strong leakage than the Shannon MI does.
--
--   Differences from the source:
--   - encoding: the posterior $p_{S\mid L}(s\mid l)$ of the leakage model → $p_S(s)\,r(s,l)$, with $r$ the real value of the Radon–Nikodym derivative of Eq. (2), of the joint law against the product of its marginals; reason: the source states this relation itself on p. 9 ($r=p_{S\mid L=l}/p_S$); it is the posterior for a general leakage space, and it is determined for almost every $l$
--   - encoding: random variables $(S,L)$ on an unnamed probability space → the explicit joint law $\frac1m\sum_s\delta_s\otimes\tau(s)$; reason: every quantity depends only on this law, and this sum is that law
--   - encoding: Shannon mutual information $I(\cdot;\cdot)$ in bits → `(klDiv P (P.fst.prod P.snd)).toReal / Real.log 2`; reason: Mathlib's `klDiv` is in nats and valued in $[0,\infty]$; here it is finite because the first coordinate is finite
--   - encoding: "For all $i$", with the subscript $i$ → one channel `τ`, with no index; reason: the statement for one arbitrary channel is the statement for each $\tau_i$
--   - reading: $f,g:\mathbb R^+\to\mathbb R$ → $f,g$ on all of $\mathbb R$, with $f(0)=1$ and $g(0)=1$ from Lean's $\log 0=0$, and only their values on $[0,\infty)$ used; reason: $\mathbb R^+$ must include $0$: deterministic channels, treated on pp. 5 and 22, have $r=0$, and $0\ln 0=0$ gives these values
--   - encoding: "Let $f(r)$ and $g(r)$ be measurable functions" → measurability is a property of the two definitions and not a clause of the statement; reason: $f$ and $g$ are explicit; their measurability is checked in the mission's verification module
-- source:
--   Rei Ueno, A Spectral Theory of Local-to-Global Leakage, STOC 2027 submission #326 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/326.pdf, Lemma 1 with Eq. (2), p. 9; proof in Appendix B.2, p. 28

import Mathlib
import Definitions.Def_LeakageSpectral_Shannon_Divergences
import Definitions.Def_LeakageSpectral_Shannon_JointLaw
import Definitions.Def_LeakageSpectral_Shannon_ShareModel
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LeakageSpectral.Shannon

/-- Lemma 1, p. 9: `μ` is a probability measure, the likelihood ratio has the second form of Eq. (2), and
`I_χ²(S; L) = α I(S; L)` with `α = ln(2) E_μ g(r)`. -/
theorem lemma_1 {G : Type*} [AddCommGroup G] [Fintype G] [MeasurableSpace G] [DiscreteMeasurableSpace G]
    {L : Type*} [MeasurableSpace L] (τ : Kernel G L) [IsMarkovKernel τ]
    (hdep : 0 < shannonMI (localJoint τ)) :
    IsProbabilityMeasure (sharpnessMeasure τ) ∧
      (∀ s : G, ∀ᵐ l ∂(localJoint τ).snd,
        likelihoodRatio (localJoint τ) s l = ((τ s).rnDeriv (localJoint τ).snd l).toReal) ∧
      chiSquareMI (localJoint τ) = sharpness τ * shannonMI (localJoint τ) := by sorry

end LeakageSpectral.Shannon
