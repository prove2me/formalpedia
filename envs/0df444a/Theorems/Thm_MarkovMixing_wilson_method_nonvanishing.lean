-- Prove2me | Theorems.Thm_MarkovMixing_wilson_method_nonvanishing
-- name    : MarkovMixing.wilson_method_nonvanishing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T16:29:35.012184+00:00
-- url     : https://prove2.me/theorems/ff80e21c-d35f-43cf-8b9c-88a3a3a33fa9
-- title:
--   Theorem 13.5 -- Wilson's method for lower bounds
-- statement:
--   Let $P$ be an irreducible aperiodic Markov chain on a finite state space $V$ with stationary distribution $\pi$. Write $(Pf)(x)=\sum_y P(x,y)f(y)$ for the action of the chain on functions, and recall that $f$ is an **eigenfunction** with eigenvalue $\lambda$ when $f$ is not identically zero and $Pf=\lambda f$.
--
--   Suppose $\Phi:V\to\mathbb R$ is such an eigenfunction, with eigenvalue $\lambda$ in the range
--   $$\tfrac12<\lambda<1,$$
--   and let $R>0$ bound the expected squared one-step increment of $\Phi$ from every state:
--   $$\sum_{y}P(x,y)\bigl(\Phi(y)-\Phi(x)\bigr)^2\;\le\;R\qquad\text{for all }x\in V.$$
--   As above, $\|\mu-\nu\|_{TV}=\max_{A\subseteq V}|\mu(A)-\nu(A)|$ is the total variation distance, $d(t)=\max_x\|P^t(x,\cdot)-\pi\|_{TV}$, and $t_{\mathrm{mix}}(\varepsilon)=\min\{t : d(t)\le\varepsilon\}$ is the mixing time.
--
--   **Wilson's method** (Levin–Peres–Wilmer, Theorem 13.5) asserts that for every tolerance $0<\varepsilon<1$ and every state $x$ at which the eigenfunction does not vanish, $\Phi(x)\neq0$,
--   $$t_{\mathrm{mix}}(\varepsilon)\;\ge\;\frac{1}{2\log(1/\lambda)}\left[\log\!\left(\frac{(1-\lambda)\,\Phi(x)^2}{2R}\right)+\log\!\left(\frac{1-\varepsilon}{\varepsilon}\right)\right].$$
--
--   The shape of the bound is worth reading slowly. The prefactor $1/(2\log(1/\lambda))$ is essentially the relaxation time — for $\lambda$ close to $1$, $\log(1/\lambda)\approx 1-\lambda$ — so Wilson's method always recovers a lower bound of relaxation-time order. The gain is in the bracket: a *geometric* term $\log\bigl((1-\lambda)\Phi(x)^2/(2R)\bigr)$ that grows when the eigenfunction is large at the starting state relative to the size of its one-step increments. Choosing a good test eigenfunction therefore multiplies the trivial bound by a logarithmic factor, and this is what produces sharp lower bounds — matching the upper bounds up to constants — for chains such as the lazy random walk on the hypercube and the random adjacent transposition shuffle.
--
--   *A note on the non-vanishing hypothesis.* The book writes "for any $x\in\Omega$", reading the bracket in the extended reals: at a state where $\Phi(x)=0$ the logarithm is $-\infty$ and the bound is empty. The Lean logarithm is total, with $\log 0=0$, so such states would silently turn into a genuine — and strictly stronger than the source — lower bound. The hypothesis $\Phi(x)\neq0$ restricts the claim to the states where the book's bound has content.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 13.2, Theorem 13.5, Eq. (13.3), p. 172

import Definitions.Def_mm_spectral
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MarkovMixing

/-- **Theorem 13.5, Wilson's method** (LPW): if `Φ` is an eigenfunction with
eigenvalue `λ ∈ (1/2, 1)` and the one-step increments of `Φ` have second
moment at most `R`, then for any starting state `x`,
`t_mix(ε) ≥ (2 log(1/λ))⁻¹ [log((1−λ)Φ(x)²/(2R)) + log((1−ε)/ε)]`.

The bound is stated at states where `Φ` does not vanish.  LPW write "for any
`x ∈ Ω`", reading the bound in the extended reals: at a state with `Φ(x) = 0`
the logarithm is `−∞` and the inequality says nothing.  `Real.log` is total in
Lean (`log 0 = 0`), which would turn that empty case into a genuine — and
strictly stronger than the book's — lower bound, so `Φ x ≠ 0` is hypothesized
instead. -/
theorem wilson_method_nonvanishing {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P)
    (hap : Aperiodic P) (π : V → ℝ) (hπ : IsStationary P π)
    (Φ : V → ℝ) (hΦ : Φ ≠ 0) (lam : ℝ) (heig : P.mulVec Φ = lam • Φ)
    (hlam1 : 1 / 2 < lam) (hlam2 : lam < 1)
    (R : ℝ) (hR : 0 < R)
    (hstep : ∀ x : V, ∑ y, P x y * (Φ y - Φ x) ^ 2 ≤ R)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (x : V) (hΦx : Φ x ≠ 0) :
    (2 * Real.log (1 / lam))⁻¹ *
        (Real.log ((1 - lam) * Φ x ^ 2 / (2 * R)) + Real.log ((1 - ε) / ε)) ≤
      (mixingTime P π ε : ℝ) := by
  sorry

end MarkovMixing
