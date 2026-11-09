-- Prove2me | Theorems.Thm_LeakageSpectral_Shannon_parseval_local
-- name    : LeakageSpectral.Shannon.parseval_local
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:04.78739+00:00
-- url     : https://prove2.me/theorems/257396f0-389e-4548-ae2a-1105c84f0e99
-- title:
--   §3.1 display, p. 7 — Parseval for the local $\chi^2$-MI
-- statement:
--   Let $S$ be uniform on the finite abelian group $\mathbb G$, let the leakage $L$ be drawn from a Markov kernel given $S$, with values in any measurable space, and assume $I(S;L)>0$, the paper's standing assumption. Then the $\chi^2$-mutual information is the sum of the non-trivial Fourier modes of leakage:
--
--   $$
--   I_{\chi^2}(S;L)=\sum_{w\neq0}\lambda(w).
--   $$
--
--   This identity makes the $\chi^2$-MI the right local quantity for a spectral analysis.
--
--   Differences from the source:
--   - encoding: the posterior $p_{S\mid L}(s\mid l)$ of the leakage model → $p_S(s)\,r(s,l)$, with $r$ the real value of the Radon–Nikodym derivative of Eq. (2), of the joint law against the product of its marginals; reason: the source states this relation itself on p. 9 ($r=p_{S\mid L=l}/p_S$); it is the posterior for a general leakage space, and it is determined for almost every $l$
--   - encoding: frequencies $w\in\mathcal W$ with characters $\chi_w$, and $w\neq0$ → `AddChar G ℂ` and its non-trivial elements (`NontrivialChar G`); reason: the same objects: the character group of $\mathbb G$, indexed directly rather than through $\mathcal W$
--   - encoding: random variables $(S,L)$ on an unnamed probability space → the explicit joint law $\frac1m\sum_s\delta_s\otimes\tau(s)$; reason: every quantity depends only on this law, and this sum is that law
--   - encoding: Shannon mutual information $I(\cdot;\cdot)$ in bits → `(klDiv P (P.fst.prod P.snd)).toReal / Real.log 2`; reason: Mathlib's `klDiv` is in nats and valued in $[0,\infty]$; here it is finite because the first coordinate is finite
-- source:
--   Rei Ueno, A Spectral Theory of Local-to-Global Leakage, STOC 2027 submission #326 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/326.pdf, §3.1 display, p. 7

import Mathlib
import Definitions.Def_LeakageSpectral_Shannon_Divergences
import Definitions.Def_LeakageSpectral_Shannon_JointLaw
import Definitions.Def_LeakageSpectral_Shannon_ShareModel
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LeakageSpectral.Shannon

/-- §3.1 display, p. 7 (Parseval): `I_χ²(S; L) = ∑_{w ≠ 0} λ(w)`. -/
theorem parseval_local {G : Type*} [AddCommGroup G] [Fintype G] [MeasurableSpace G] [DiscreteMeasurableSpace G]
    {L : Type*} [MeasurableSpace L] (τ : Kernel G L) [IsMarkovKernel τ]
    (hdep : 0 < shannonMI (localJoint τ)) :
    chiSquareMI (localJoint τ) = ∑ w : NontrivialChar G, fourierMode τ w := by sorry

end LeakageSpectral.Shannon
