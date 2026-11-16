-- Prove2me | Theorems.Thm_LeakageSpectral_Shannon_Supplement_theorem_7
-- name    : LeakageSpectral.Shannon.Supplement.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:42:46.636417+00:00
-- url     : https://prove2.me/theorems/0b12f088-90c3-4846-a5eb-018ab99c9d56
-- title:
--   Theorem 7, p. 15 — necessary and sufficient condition for exponential tightness
-- statement:
--   Let $\mathbb G$ be a finite abelian group with the discrete $\sigma$-algebra and $\tau$ a leakage channel (a Markov kernel from $\mathbb G$ to a measurable space) with $I(S;L)>0$, used for every share (i.i.d. leakage); let $q$ be its normalized Fourier leakage spectrum and $H_\infty(q)=-\log_2\max_{w\ne0}q(w)$. The **spectral-alignment relaxation** bounds the global leakage by the product of the local magnitudes, i.e. it drops the factor $\kappa_d\le1$ from the exact formulas of Theorems 1 and 2. The relaxation is **exponentially tight** if the ratio (bound)/(true value) is $2^{o(d)}$ as $d\to\infty$.
--
--   1. ($\chi^2$-MI) With $M=I_{\chi^2}(S;L)$:
--   $$\frac1d\log_2\frac{M^{d+1}}{I_{\chi^2}(Z;X)}\xrightarrow[d\to\infty]{}0\iff H_\infty(q)=0.$$
--   2. (Shannon MI) If moreover $\rho^*<1$, then with $\alpha$ the leakage sharpness:
--   $$\frac1d\log_2\frac{(\alpha I(S;L))^{d+1}}{I(Z;X)}\xrightarrow[d\to\infty]{}0\iff H_\infty(q)=0.$$
--
--   Here $Z=S_0+\dots+S_d$ and $X=(L_0,\dots,L_d)$. The condition $H_\infty(q)=0$ means that $q$ is one-hot: the leakage is concentrated on a single Fourier character.
--
--   Differences from the source:
--
--   - reading: "spectral-alignment relaxation" (not formally defined) → the bound I_χ²(S;L)^{d+1} (χ² clause) and (α I(S;L))^{d+1} (Shannon clause), i.e. κ_d replaced by 1; reason: the magnitude-only bounds of §3.2 and §4.4 ("Existing MI-only bounds"), the exact formulas of Theorems 1 and 2 without κ_d; the constant 1/(2 ln 2) does not affect the exponent
--   - reading: "exponentially tight" → (1/d)·log₂(bound / true value) → 0; reason: the opposite of the "exponential slack" exp(Θ(d)) discussed in §3.2 and §4.4
--   - reading: one condition for "the" relaxation → two clauses: χ²-MI, and Shannon MI under ρ* < 1; reason: the proof cites Theorem 4 (χ²) and Corollary 2 (Shannon, which assumes ρ* < 1)
--   - reading: a channel without share index ("we may omit the subscript i, assuming that the leakages are i.i.d.", §2.1, p. 5) → one Markov kernel τ used for every share: globalJoint (fun _ => τ) d; reason: the paper's standing i.i.d. convention for unindexed statements
--   - encoding: standing assumption I(S;L) > 0 of §2.1, p. 5, not repeated in the theorem → hypothesis 0 < shannonMI (localJoint τ); reason: the standing assumption of the section, written as a binder as in the base mission
-- source:
--   Rei Ueno, A Spectral Theory of Local-to-Global Leakage, STOC 2027 submission #326 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/326.pdf, Theorem 7, p. 15 (with §3.2 and §4.4)

import Mathlib
import Definitions.Def_LeakageSpectral_Shannon_Divergences
import Definitions.Def_LeakageSpectral_Shannon_JointLaw
import Definitions.Def_LeakageSpectral_Shannon_ShareModel
import Definitions.Def_LeakageSpectral_Shannon_Supplement_Defs
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LeakageSpectral.Shannon.Supplement

/-- Ueno, STOC 2027 submission #326, Theorem 7, p. 15: the spectral-alignment relaxation is
exponentially tight iff `H∞(q) = 0`. For i.i.d. leakage through one channel `τ` with `I(S; L) > 0`,
the relaxation drops the factor `κ_d`, bounding the global leakage by the product of the local
magnitudes; it is exponentially tight when the ratio (bound / true value) is `2^{o(d)}`.
χ² clause: `(1/d) log₂ (I_χ²(S; L)^{d+1} / I_χ²(Z; X)) → 0` iff `H∞(q) = 0`.
Shannon clause, under `ρ* < 1`: `(1/d) log₂ ((α I(S; L))^{d+1} / I(Z; X)) → 0` iff `H∞(q) = 0`. -/
theorem theorem_7 {G : Type*} [AddCommGroup G] [Fintype G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G] {L : Type*} [MeasurableSpace L] (τ : Kernel G L) [IsMarkovKernel τ]
    (hdep : 0 < shannonMI (localJoint τ)) :
    (Tendsto (fun d : ℕ => (1 / (d : ℝ)) *
        Real.logb 2 (chiSquareMI (localJoint τ) ^ (d + 1) /
          chiSquareMI (globalJoint (fun _ : ℕ => τ) d))) atTop (𝓝 0) ↔
      minEntropy (spectrum τ) = 0) ∧
    (rhoStar (fun _ : ℕ => τ) < 1 →
      (Tendsto (fun d : ℕ => (1 / (d : ℝ)) *
          Real.logb 2 ((sharpness τ * shannonMI (localJoint τ)) ^ (d + 1) /
            shannonMI (globalJoint (fun _ : ℕ => τ) d))) atTop (𝓝 0) ↔
        minEntropy (spectrum τ) = 0)) := by sorry

end LeakageSpectral.Shannon.Supplement
