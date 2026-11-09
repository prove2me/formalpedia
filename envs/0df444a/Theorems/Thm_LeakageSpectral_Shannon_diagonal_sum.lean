-- Prove2me | Theorems.Thm_LeakageSpectral_Shannon_diagonal_sum
-- name    : LeakageSpectral.Shannon.diagonal_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:57.322619+00:00
-- url     : https://prove2.me/theorems/c3aaf183-210f-4e36-8d51-d0d32fb6201c
-- title:
--   Appendix B.1 display, p. 27 — only diagonal modes survive
-- statement:
--   In the setting of additive sharing with independent uniform shares and $I(S_i;L_i)>0$ for all $i$,
--
--   $$
--   I_{\chi^2}(Z;X)=\sum_{w\neq0}\prod_{i=0}^{d}\lambda_i(w),
--   $$
--
--   where $\lambda_i$ is the Fourier mode of leakage of the channel $\tau_i$. Only products of the modes at one common frequency appear; cross-mode combinations do not contribute.
--
--   Differences from the source:
--   - encoding: the posterior $p_{S\mid L}(s\mid l)$ of the leakage model → $p_S(s)\,r(s,l)$, with $r$ the real value of the Radon–Nikodym derivative of Eq. (2), of the joint law against the product of its marginals; reason: the source states this relation itself on p. 9 ($r=p_{S\mid L=l}/p_S$); it is the posterior for a general leakage space, and it is determined for almost every $l$
--   - encoding: the posterior $p_{Z\mid X}(z\mid x)$ → $p_Z(z)\,r(z,x)$, with $r$ the real value of the Radon–Nikodym derivative of the joint law of $(Z,X)$ against the product of its marginals; reason: the source says so on p. 29 ("precisely, $r$ is defined as the Radon–Nikodym derivative in Equation (2)")
--   - encoding: frequencies $w\in\mathcal W$ with characters $\chi_w$, and $w\neq0$ → `AddChar G ℂ` and its non-trivial elements (`NontrivialChar G`); reason: the same objects: the character group of $\mathbb G$, indexed directly rather than through $\mathcal W$
--   - reading: $Z=S_0+\dots+S_d$, with §1.1 opening "Let $Z$ be a random variable" → the shares are independent and uniform on $G$, each $L_i$ depends on $S_i$ alone, and $Z$ is their sum, hence uniform; reason: the proofs use "the independence assumption" (p. 27) and a uniform $p_Z$; with an arbitrary $Z$ the statements fail: $G=\mathbb Z_2$, $Z\equiv0$, $S_1=S_0$ uniform, channel $(1+l(-1)^s/2)/2$ on $l=\pm1$ has $I(Z;X)=0$ and a positive right-hand side
--   - encoding: random variables $(Z,X)$ on an unnamed probability space → the explicit joint law $m^{-(d+1)}\sum_s\delta_{s_0+\dots+s_d}\otimes\bigotimes_i\tau_i(s_i)$; reason: every quantity depends only on this law, and this sum is that law
--   - encoding: shares $i=0,\dots,d$ of a family of channels → `i : Fin (d + 1)`, with channels `τ : ∀ i : ℕ, Kernel G (L i)`; reason: the same finite family; the values of `τ` beyond index $d$ play no role
--   - encoding: Shannon mutual information $I(\cdot;\cdot)$ in bits → `(klDiv P (P.fst.prod P.snd)).toReal / Real.log 2`; reason: Mathlib's `klDiv` is in nats and valued in $[0,\infty]$; here it is finite because the first coordinate is finite
-- source:
--   Rei Ueno, A Spectral Theory of Local-to-Global Leakage, STOC 2027 submission #326 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/326.pdf, Appendix B.1 display after Eq. (15), p. 27; also proof of Theorem 1, p. 8

import Mathlib
import Definitions.Def_LeakageSpectral_Shannon_Divergences
import Definitions.Def_LeakageSpectral_Shannon_JointLaw
import Definitions.Def_LeakageSpectral_Shannon_ShareModel
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LeakageSpectral.Shannon

/-- Appendix B.1 display, p. 27: `I_χ²(Z; X) = ∑_{w ≠ 0} ∏_{i=0}^d λ_i(w)`. -/
theorem diagonal_sum {G : Type*} [AddCommGroup G] [Fintype G] [MeasurableSpace G] [DiscreteMeasurableSpace G]
    {L : ℕ → Type*} [∀ i, MeasurableSpace (L i)] (τ : ∀ i, Kernel G (L i)) [∀ i, IsMarkovKernel (τ i)]
    (d : ℕ) (hdep : ∀ i : Fin (d + 1), 0 < shannonMI (localJoint (τ i))) :
    chiSquareMI (globalJoint τ d) =
      ∑ w : NontrivialChar G, ∏ i : Fin (d + 1), fourierMode (τ i) w := by sorry

end LeakageSpectral.Shannon
