-- Prove2me | Theorems.Thm_LeakageSpectral_Shannon_b3_expansion
-- name    : LeakageSpectral.Shannon.b3_expansion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:08.855464+00:00
-- url     : https://prove2.me/theorems/03ec07e7-84bc-41cf-9d2c-53c0cf553fca
-- title:
--   Appendix B.3 display, p. 29 — Shannon expansion in $\chi^2$-MI with explicit error
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. In the setting of additive sharing with independent uniform shares, let $I(S_i;L_i)>0$ for all $i$ and let $\rho^*<1$. For every $d$ with $(m-1)(\rho^*)^{d+1}<1$, there is a real $E$ with $|E|\le C(m-1)(\rho^*)^{d+1}$ such that
--
--   $$
--   I(Z;X)=\frac{1+E}{2\ln2}\,I_{\chi^2}(Z;X).
--   $$
--
--   Since $(m-1)(\rho^*)^{d+1}\to0$, this covers all large $d$. It gives the explicit error term of the expansion, which the discussion after Theorem 2 on p. 10 also quotes.
--
--   Differences from the source:
--   - encoding: the posterior $p_{Z\mid X}(z\mid x)$ → $p_Z(z)\,r(z,x)$, with $r$ the real value of the Radon–Nikodym derivative of the joint law of $(Z,X)$ against the product of its marginals; reason: the source says so on p. 29 ("precisely, $r$ is defined as the Radon–Nikodym derivative in Equation (2)")
--   - encoding: frequencies $w\in\mathcal W$ with characters $\chi_w$, and $w\neq0$ → `AddChar G ℂ` and its non-trivial elements (`NontrivialChar G`); reason: the same objects: the character group of $\mathbb G$, indexed directly rather than through $\mathcal W$
--   - reading: $Z=S_0+\dots+S_d$, with §1.1 opening "Let $Z$ be a random variable" → the shares are independent and uniform on $G$, each $L_i$ depends on $S_i$ alone, and $Z$ is their sum, hence uniform; reason: the proofs use "the independence assumption" (p. 27) and a uniform $p_Z$; with an arbitrary $Z$ the statements fail: $G=\mathbb Z_2$, $Z\equiv0$, $S_1=S_0$ uniform, channel $(1+l(-1)^s/2)/2$ on $l=\pm1$ has $I(Z;X)=0$ and a positive right-hand side
--   - encoding: random variables $(Z,X)$ on an unnamed probability space → the explicit joint law $m^{-(d+1)}\sum_s\delta_{s_0+\dots+s_d}\otimes\bigotimes_i\tau_i(s_i)$; reason: every quantity depends only on this law, and this sum is that law
--   - encoding: Shannon mutual information $I(\cdot;\cdot)$ in bits → `(klDiv P (P.fst.prod P.snd)).toReal / Real.log 2`; reason: Mathlib's `klDiv` is in nats and valued in $[0,\infty]$; here it is finite because the first coordinate is finite
--   - encoding: $\rho^*$ as a real number → `rhoStar τ`, valued in $[0,\infty]$, with its real value where a power is taken; reason: the supremum in $[0,\infty]$ has no junk value; below $1$ it is the same number
--   - generalization: $O((m-1)(\rho^*)^{d+1})$ "as $d\to\infty$ for given $m$" → one absolute constant $C$, independent of $G$, the channels and $d$, at every $d$ with $(m-1)(\rho^*)^{d+1}<1$; reason: Lemma 3 gives an absolute constant uniformly in the radius; since the bound tends to $0$, this specializes to the printed statement
--   - encoding: $1+O(\cdot)$ → an explicit real $E$ with $|E|\le C(m-1)(\rho^*)^{d+1}$; reason: the meaning of the $O$
-- source:
--   Rei Ueno, A Spectral Theory of Local-to-Global Leakage, STOC 2027 submission #326 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/326.pdf, Appendix B.3 display, p. 29

import Mathlib
import Definitions.Def_LeakageSpectral_Shannon_Divergences
import Definitions.Def_LeakageSpectral_Shannon_JointLaw
import Definitions.Def_LeakageSpectral_Shannon_ShareModel
open MeasureTheory ProbabilityTheory
open scoped ENNReal
universe uG vL

namespace LeakageSpectral.Shannon

/-- Appendix B.3 display, p. 29: `I(Z; X) = (1 + O((m - 1)(ρ*)^{d+1})) / (2 ln 2) · I_χ²(Z; X)`, with one
absolute constant, at every `d` where `(m - 1)(ρ*)^{d+1} < 1`. -/
theorem b3_expansion :
    ∃ C : ℝ, 0 < C ∧ ∀ {G : Type uG} [AddCommGroup G] [Fintype G] [MeasurableSpace G]
      [DiscreteMeasurableSpace G] {L : ℕ → Type vL} [∀ i, MeasurableSpace (L i)]
      (τ : ∀ i, Kernel G (L i)) [∀ i, IsMarkovKernel (τ i)],
      (∀ i, 0 < shannonMI (localJoint (τ i))) → rhoStar τ < 1 →
      ∀ d : ℕ, ((Fintype.card G : ℝ) - 1) * (rhoStar τ).toReal ^ (d + 1) < 1 →
        ∃ E : ℝ, |E| ≤ C * (((Fintype.card G : ℝ) - 1) * (rhoStar τ).toReal ^ (d + 1)) ∧
          shannonMI (globalJoint τ d) =
            (1 + E) / (2 * Real.log 2) * chiSquareMI (globalJoint τ d) := by sorry

end LeakageSpectral.Shannon
