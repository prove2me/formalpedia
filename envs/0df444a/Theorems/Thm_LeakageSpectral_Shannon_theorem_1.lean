-- Prove2me | Theorems.Thm_LeakageSpectral_Shannon_theorem_1
-- name    : LeakageSpectral.Shannon.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:39.099446+00:00
-- url     : https://prove2.me/theorems/fd81f5ff-08ad-46ff-8d1c-049b6438b512
-- title:
--   Theorem 1, p. 8 — exact spectral decomposition
-- statement:
--   In the setting of additive sharing with independent uniform shares and $I(S_i;L_i)>0$ for all $i$, each normalized spectrum $q_i(w)=\lambda_i(w)/\sum_{w'\neq0}\lambda_i(w')$ is a probability distribution on the non-trivial characters, and the global leakage decomposes exactly as
--
--   $$
--   I_{\chi^2}(Z;X)=\kappa_d\prod_{i=0}^{d}I_{\chi^2}(S_i;L_i),
--   $$
--
--   where $\kappa_d=\Pr[W_0=W_1=\dots=W_d]$, $W_i\sim q_i$ independent, is the spectral alignment factor. If moreover $q_0=q_1=\dots=q_d=q$, then
--
--   $$
--   \kappa_d=2^{-dH_{d+1}(q)},
--   $$
--
--   where $H_{d+1}$ is the Rényi entropy of order $d+1$.
--
--   The theorem separates the global leakage into local magnitudes and a structural factor that no local magnitude determines. It holds at every $d\ge0$ and for channels that may differ.
--
--   Differences from the source:
--   - encoding: the posterior $p_{S\mid L}(s\mid l)$ of the leakage model → $p_S(s)\,r(s,l)$, with $r$ the real value of the Radon–Nikodym derivative of Eq. (2), of the joint law against the product of its marginals; reason: the source states this relation itself on p. 9 ($r=p_{S\mid L=l}/p_S$); it is the posterior for a general leakage space, and it is determined for almost every $l$
--   - encoding: the posterior $p_{Z\mid X}(z\mid x)$ → $p_Z(z)\,r(z,x)$, with $r$ the real value of the Radon–Nikodym derivative of the joint law of $(Z,X)$ against the product of its marginals; reason: the source says so on p. 29 ("precisely, $r$ is defined as the Radon–Nikodym derivative in Equation (2)")
--   - encoding: frequencies $w\in\mathcal W$ with characters $\chi_w$, and $w\neq0$ → `AddChar G ℂ` and its non-trivial elements (`NontrivialChar G`); reason: the same objects: the character group of $\mathbb G$, indexed directly rather than through $\mathcal W$
--   - reading: $Z=S_0+\dots+S_d$, with §1.1 opening "Let $Z$ be a random variable" → the shares are independent and uniform on $G$, each $L_i$ depends on $S_i$ alone, and $Z$ is their sum, hence uniform; reason: the proofs use "the independence assumption" (p. 27) and a uniform $p_Z$; with an arbitrary $Z$ the statements fail: $G=\mathbb Z_2$, $Z\equiv0$, $S_1=S_0$ uniform, channel $(1+l(-1)^s/2)/2$ on $l=\pm1$ has $I(Z;X)=0$ and a positive right-hand side
--   - encoding: random variables $(Z,X)$ on an unnamed probability space → the explicit joint law $m^{-(d+1)}\sum_s\delta_{s_0+\dots+s_d}\otimes\bigotimes_i\tau_i(s_i)$; reason: every quantity depends only on this law, and this sum is that law
--   - encoding: shares $i=0,\dots,d$ of a family of channels → `i : Fin (d + 1)`, with channels `τ : ∀ i : ℕ, Kernel G (L i)`; reason: the same finite family; the values of `τ` beyond index $d$ play no role
--   - encoding: Shannon mutual information $I(\cdot;\cdot)$ in bits → `(klDiv P (P.fst.prod P.snd)).toReal / Real.log 2`; reason: Mathlib's `klDiv` is in nats and valued in $[0,\infty]$; here it is finite because the first coordinate is finite
--   - encoding: "let $q_i$ … be a probability distribution" → a clause of the conclusion: $q_i\ge0$ and $\sum_w q_i(w)=1$; reason: the source asserts it; it is what makes $\kappa_d$ a probability, and it follows from the standing assumption
--   - reading: "If leakages are independent and identically distributed (i.i.d) for all shares (i.e., $q_0=q_1=\dots=q_d$)" → the hypothesis is equality of the spectra, not of the channels; reason: the source's "i.e." and its use of the clause on p. 12 fix the hypothesis to the spectra; equal channels are a special case
--   - encoding: $H_{d+1}(q)$ at $d=0$, where the order is $1$ → $H_1$ is the Shannon entropy; reason: the standard value at order $1$; the exponent $-dH_{d+1}$ is $0$ there in any case
-- source:
--   Rei Ueno, A Spectral Theory of Local-to-Global Leakage, STOC 2027 submission #326 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/326.pdf, Theorem 1, p. 8; proof in Appendix B.1, pp. 27–28

import Mathlib
import Definitions.Def_LeakageSpectral_Shannon_Divergences
import Definitions.Def_LeakageSpectral_Shannon_JointLaw
import Definitions.Def_LeakageSpectral_Shannon_ShareModel
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LeakageSpectral.Shannon

/-- Theorem 1, p. 8: each `q_i` is a probability distribution on the non-trivial characters,
`I_χ²(Z; X) = κ_d ∏_{i=0}^d I_χ²(S_i; L_i)`, and `κ_d = 2^{-d H_{d+1}(q)}` when
`q₀ = q₁ = ⋯ = q_d = q`. -/
theorem theorem_1 {G : Type*} [AddCommGroup G] [Fintype G] [MeasurableSpace G] [DiscreteMeasurableSpace G]
    {L : ℕ → Type*} [∀ i, MeasurableSpace (L i)] (τ : ∀ i, Kernel G (L i)) [∀ i, IsMarkovKernel (τ i)]
    (d : ℕ) (hdep : ∀ i : Fin (d + 1), 0 < shannonMI (localJoint (τ i))) :
    (∀ i : Fin (d + 1), (∀ w, 0 ≤ spectrum (τ i) w) ∧ ∑ w, spectrum (τ i) w = 1) ∧
      chiSquareMI (globalJoint τ d) =
        spectralAlignment τ d * ∏ i : Fin (d + 1), chiSquareMI (localJoint (τ i)) ∧
      ∀ q : NontrivialChar G → ℝ, (∀ i : Fin (d + 1), spectrum (τ i) = q) →
        spectralAlignment τ d = (2 : ℝ) ^ (-(d : ℝ) * renyiEntropy ((d : ℝ) + 1) q) := by sorry

end LeakageSpectral.Shannon
