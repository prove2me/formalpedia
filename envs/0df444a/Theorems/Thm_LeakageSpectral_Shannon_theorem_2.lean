-- Prove2me | Theorems.Thm_LeakageSpectral_Shannon_theorem_2
-- name    : LeakageSpectral.Shannon.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:20.724646+00:00
-- url     : https://prove2.me/theorems/528446b0-44cc-4078-bec9-c67e5ed39c27
-- title:
--   Theorem 2, p. 10 — sharp asymptotic expansion of the global Shannon leakage
-- statement:
--   Let $\mathbb G$ be a finite abelian group with the discrete $\sigma$-algebra, and let $(\tau_i)_{i\ge0}$ be Markov kernels from $\mathbb G$ to measurable spaces, possibly different. Let the shares $S_i$ be independent and uniform on $\mathbb G$, let $L_i$ be drawn from $\tau_i$ given $S_i$ alone, and put $Z=S_0+\dots+S_d$ and $X=(L_0,\dots,L_d)$. Assume $I(S_i;L_i)>0$ for all $i$, the paper's standing assumption, and the strict weak worst-case condition
--
--   $$
--   \rho^*=\sup_i\max_{w\neq0}\operatorname*{ess\,sup}_l|\hat p_{S_i\mid L_i}(w\mid l)|<1.
--   $$
--
--   Then, as $d\to\infty$,
--
--   $$
--   I(Z;X)=\frac{1+o(1)}{2\ln2}\,\kappa_d\prod_{i=0}^{d}\alpha_i I(S_i;L_i)=\Theta\Big(\kappa_d\prod_{i=0}^{d}\alpha_i I(S_i;L_i)\Big),
--   $$
--
--   where $\kappa_d$ is the spectral alignment factor and $\alpha_i$ is the leakage sharpness of $\tau_i$. Mutual information is in bits.
--
--   This is the paper's characterization of the global leakage by three factors: spectral alignment, leakage sharpness and local mutual information.
--
--   Differences from the source:
--   - encoding: the posterior $p_{S\mid L}(s\mid l)$ of the leakage model → $p_S(s)\,r(s,l)$, with $r$ the real value of the Radon–Nikodym derivative of Eq. (2), of the joint law against the product of its marginals; reason: the source states this relation itself on p. 9 ($r=p_{S\mid L=l}/p_S$); it is the posterior for a general leakage space, and it is determined for almost every $l$
--   - encoding: the posterior $p_{Z\mid X}(z\mid x)$ → $p_Z(z)\,r(z,x)$, with $r$ the real value of the Radon–Nikodym derivative of the joint law of $(Z,X)$ against the product of its marginals; reason: the source says so on p. 29 ("precisely, $r$ is defined as the Radon–Nikodym derivative in Equation (2)")
--   - encoding: frequencies $w\in\mathcal W$ with characters $\chi_w$, and $w\neq0$ → `AddChar G ℂ` and its non-trivial elements (`NontrivialChar G`); reason: the same objects: the character group of $\mathbb G$, indexed directly rather than through $\mathcal W$
--   - reading: $Z=S_0+\dots+S_d$, with §1.1 opening "Let $Z$ be a random variable" → the shares are independent and uniform on $G$, each $L_i$ depends on $S_i$ alone, and $Z$ is their sum, hence uniform; reason: the proofs use "the independence assumption" (p. 27) and a uniform $p_Z$; with an arbitrary $Z$ the statements fail: $G=\mathbb Z_2$, $Z\equiv0$, $S_1=S_0$ uniform, channel $(1+l(-1)^s/2)/2$ on $l=\pm1$ has $I(Z;X)=0$ and a positive right-hand side
--   - encoding: random variables $(Z,X)$ on an unnamed probability space → the explicit joint law $m^{-(d+1)}\sum_s\delta_{s_0+\dots+s_d}\otimes\bigotimes_i\tau_i(s_i)$; reason: every quantity depends only on this law, and this sum is that law
--   - encoding: Shannon mutual information $I(\cdot;\cdot)$ in bits → `(klDiv P (P.fst.prod P.snd)).toReal / Real.log 2`; reason: Mathlib's `klDiv` is in nats and valued in $[0,\infty]$; here it is finite because the first coordinate is finite
--   - encoding: $\rho^*$ as a real number → `rhoStar τ`, valued in $[0,\infty]$, with its real value where a power is taken; reason: the supremum in $[0,\infty]$ has no junk value; below $1$ it is the same number
--   - encoding: $\frac{1+o(1)}{2\ln2}\,\kappa_d\prod_i\alpha_iI(S_i;L_i)$ → a sequence $\varepsilon_d\to0$ with $I(Z;X)=\frac{1+\varepsilon_d}{2\ln2}\kappa_d\prod_i\alpha_iI(S_i;L_i)$ for all large $d$; reason: the meaning of $1+o(1)$; a ratio form would divide by $\kappa_d$, which can be $0$ for different channels (then $I(Z;X)=0$ as well)
--   - encoding: $=\Theta(\cdot)$ as $d\to\infty$ → Mathlib's `Asymptotics.IsTheta` along `atTop`; reason: the same notion
-- source:
--   Rei Ueno, A Spectral Theory of Local-to-Global Leakage, STOC 2027 submission #326 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/326.pdf, Theorem 2, p. 10; proof in Appendix B.3, p. 29

import Mathlib
import Definitions.Def_LeakageSpectral_Shannon_Divergences
import Definitions.Def_LeakageSpectral_Shannon_JointLaw
import Definitions.Def_LeakageSpectral_Shannon_ShareModel
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LeakageSpectral.Shannon

/-- Theorem 2, p. 10: if `ρ* < 1`, then as `d → ∞`,
`I(Z; X) = (1 + o(1)) / (2 ln 2) · κ_d ∏_{i=0}^d α_i I(S_i; L_i) = Θ(κ_d ∏_{i=0}^d α_i I(S_i; L_i))`. -/
theorem theorem_2 {G : Type*} [AddCommGroup G] [Fintype G] [MeasurableSpace G] [DiscreteMeasurableSpace G]
    {L : ℕ → Type*} [∀ i, MeasurableSpace (L i)] (τ : ∀ i, Kernel G (L i)) [∀ i, IsMarkovKernel (τ i)]
    (hdep : ∀ i, 0 < shannonMI (localJoint (τ i))) (hρ : rhoStar τ < 1) :
    (∃ ε : ℕ → ℝ, Filter.Tendsto ε Filter.atTop (nhds 0) ∧
        ∀ᶠ d in Filter.atTop,
          shannonMI (globalJoint τ d) =
            (1 + ε d) / (2 * Real.log 2) * spectralAlignment τ d *
              ∏ i : Fin (d + 1), (sharpness (τ i) * shannonMI (localJoint (τ i)))) ∧
      (fun d => shannonMI (globalJoint τ d)) =Θ[Filter.atTop]
        fun d => spectralAlignment τ d *
          ∏ i : Fin (d + 1), (sharpness (τ i) * shannonMI (localJoint (τ i))) := by sorry

end LeakageSpectral.Shannon
