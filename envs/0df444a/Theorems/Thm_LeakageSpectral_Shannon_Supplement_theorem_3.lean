-- Prove2me | Theorems.Thm_LeakageSpectral_Shannon_Supplement_theorem_3
-- name    : LeakageSpectral.Shannon.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:39:16.02189+00:00
-- url     : https://prove2.me/theorems/c5bb8215-c1b7-4cfa-80f1-2ccc0958500b
-- title:
--   Theorem 3, p. 11 — realizability of spectrally distinct leakage channels
-- statement:
--   Let $\mathbb G$ be a finite abelian group other than $\mathbb Z_2$ and $\mathbb Z_3$ (and non-trivial), i.e. $|\mathbb G|\ge 4$, with the discrete $\sigma$-algebra. A **leakage channel** is a Markov kernel $\tau$ from $\mathbb G$ to the binary leakage space $\{0,1\}$ (the paper's $l\in\{-1,1\}$); it is **full-support** if $p_{L\mid S}(l\mid s)>0$ for every $s$ and $l$. For a channel, $S$ is uniform on $\mathbb G$, $L\sim\tau(S)$, $\lambda(w)=\mathbb E_L|\hat p_{S\mid L}(w\mid L)|^2$ is the Fourier power spectrum and $q(w)=\lambda(w)/\sum_{w'\ne0}\lambda(w')$ the normalized spectrum on the non-trivial characters. A function $q$ on the non-trivial characters is **conjugate-symmetric** if $q(\bar w)=q(w)$, where $\chi_{\bar w}(s)=\overline{\chi_w(s)}=\chi_w(-s)$.
--
--   1. For every conjugate-symmetric probability distribution $q$ on the non-trivial characters there is $c>0$ such that for every $M\in(0,c)$ some full-support binary channel $\tau$ has normalized spectrum exactly $q$ and local $\chi^2$-mutual information $I_{\chi^2}(S;L)=M$.
--   2. The set of pairs $(\tau,\tau')$ of full-support binary channels such that both satisfy the strict weak worst-case condition $\rho^*=\max_{w\neq0}\operatorname{ess\,sup}_l|\hat p_{S\mid L}(w\mid l)|<1$, $I_{\chi^2}(S;L^\tau)=I_{\chi^2}(S;L^{\tau'})>0$, and the global $\chi^2$-MI of $d+1$ shares with i.i.d. leakage have exponential rates
--   $$r=-\lim_{d\to\infty}\frac1d\log_2 I_{\chi^2}(Z;X^\tau),\qquad r'=-\lim_{d\to\infty}\frac1d\log_2 I_{\chi^2}(Z;X^{\tau'})$$
--   that exist and satisfy $r\ne r'$, is infinite.
--
--   Here $Z=S_0+\dots+S_d$ with independent uniform shares and $X=(L_0,\dots,L_d)$, $L_i\sim\tau(S_i)$. The theorem shows that the local $\chi^2$-MI and the spectral profile are independent degrees of freedom: equal local leakage does not determine the global exponent.
--
--   Differences from the source:
--
--   - encoding: 𝔾 ≠ ℤ2 nor ℤ3, a finite abelian group → 4 ≤ Fintype.card G; reason: the groups of order 2 and 3 are exactly ℤ2 and ℤ3; the trivial group has no non-trivial character and is excluded by the standing assumption I(S;L) > 0
--   - reading: "full-support stochastic channels exist with sufficiently small local χ²-MI" (realizing q) → ∃ c > 0, ∀ M ∈ (0, c), ∃ full-support binary τ with spectrum τ = q and chiSquareMI (localJoint τ) = M; reason: "sufficiently small" read as every value below a q-dependent threshold, which is what the proof gives (I_χ² = ε²/G_q² for ε ∈ (0,1)); it implies the existence of such channels with arbitrarily small local χ²-MI
--   - reading: strict weak worst-case condition printed as max_{w≠0} ess sup_l p̂_{S|L}(w|l) < 1, without absolute value → rhoStar (fun _ => τ) < 1, with |p̂|; reason: p̂ is complex-valued; Theorem 2 (p. 10) defines the same named condition with |p̂|
--   - reading: "pairs of stochastic channels τ and τ′" in the second sentence → pairs of full-support binary Markov kernels G → Bool; reason: the pairs are those built from the first sentence's full-support channels with binary leakage l ∈ {−1,1} (proof, p. 12)
--   - encoding: "strictly different exponential rates" → ∃ r r′, r ≠ r′, with the two Tendsto statements; reason: both rates exist (Theorem 4) and differ
--   - encoding: equal local χ²-MI → chiSquareMI (localJoint τ) = chiSquareMI (localJoint τ′) together with 0 < chiSquareMI (localJoint τ); reason: positivity is the standing assumption I(S;L) > 0 of §2.1
--   - encoding: "infinitely many pairs" → Set.Infinite of the set of pairs (τ, τ′); reason: the same notion
--   - reading: a channel without share index ("we may omit the subscript i, assuming that the leakages are i.i.d.", §2.1, p. 5) → one Markov kernel τ used for every share: globalJoint (fun _ => τ) d; reason: the paper's standing i.i.d. convention for unindexed statements
-- source:
--   Rei Ueno, A Spectral Theory of Local-to-Global Leakage, STOC 2027 submission #326 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/326.pdf, Theorem 3, p. 11; proof pp. 11–12

import Mathlib
import Definitions.Def_LeakageSpectral_Shannon_Divergences
import Definitions.Def_LeakageSpectral_Shannon_JointLaw
import Definitions.Def_LeakageSpectral_Shannon_ShareModel
import Definitions.Def_LeakageSpectral_Shannon_Supplement_Defs
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LeakageSpectral.Shannon.Supplement

/-- Ueno, STOC 2027 submission #326, Theorem 3, p. 11 (proof pp. 11–12): realizability of spectrally
distinct leakage channels. Let `G` be a finite abelian group other than `ℤ₂`, `ℤ₃` (and non-trivial,
by the standing assumption `I(S; L) > 0`), i.e. `|G| ≥ 4`.
(a) For every conjugate-symmetric probability distribution `q` on the non-trivial characters there is a
threshold `c > 0` such that every local χ²-MI value `M ∈ (0, c)` is attained by a full-support binary
channel whose normalized spectrum is exactly `q`.
(b) There are infinitely many pairs `(τ, τ')` of full-support binary channels with equal (positive) local
χ²-MI, both satisfying the strict weak worst-case condition `ρ* < 1` (with `|p̂|`, as in Theorem 2),
whose i.i.d. global χ²-MI have exponential rates `lim -(1/d) log₂ I_χ²(Z; X)` that exist and differ. -/
theorem theorem_3 {G : Type*} [AddCommGroup G] [Fintype G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G] (hG : 4 ≤ Fintype.card G) :
    (∀ q : NontrivialChar G → ℝ, (∀ w, 0 ≤ q w) → ∑ w, q w = 1 → IsConjSymm q →
      ∃ c : ℝ, 0 < c ∧ ∀ M : ℝ, 0 < M → M < c →
        ∃ τ : Kernel G Bool, IsMarkovKernel τ ∧ FullSupport τ ∧ spectrum τ = q ∧
          chiSquareMI (localJoint τ) = M) ∧
    {p : Kernel G Bool × Kernel G Bool |
        IsMarkovKernel p.1 ∧ IsMarkovKernel p.2 ∧ FullSupport p.1 ∧ FullSupport p.2 ∧
        rhoStar (fun _ : ℕ => p.1) < 1 ∧ rhoStar (fun _ : ℕ => p.2) < 1 ∧
        0 < chiSquareMI (localJoint p.1) ∧
        chiSquareMI (localJoint p.1) = chiSquareMI (localJoint p.2) ∧
        ∃ r r' : ℝ, r ≠ r' ∧
          Tendsto (fun d : ℕ => -(1 / (d : ℝ)) *
            Real.logb 2 (chiSquareMI (globalJoint (fun _ : ℕ => p.1) d))) atTop (𝓝 r) ∧
          Tendsto (fun d : ℕ => -(1 / (d : ℝ)) *
            Real.logb 2 (chiSquareMI (globalJoint (fun _ : ℕ => p.2) d))) atTop (𝓝 r')}.Infinite := by sorry

end LeakageSpectral.Shannon.Supplement
