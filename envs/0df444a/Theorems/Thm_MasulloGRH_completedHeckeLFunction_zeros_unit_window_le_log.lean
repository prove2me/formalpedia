-- Prove2me | Theorems.Thm_MasulloGRH_completedHeckeLFunction_zeros_unit_window_le_log
-- name    : MasulloGRH.completedHeckeLFunction_zeros_unit_window_le_log
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:31:52.492101+00:00
-- url     : https://prove2.me/theorems/4a07857f-1d72-4f66-852c-cc659d17148b
-- title:
--   Zeros of a Hecke $L$-function in a window of bounded height: $\#\{\rho:\ |\operatorname{Im}\rho-T|\le1\}\ll\log(|T|+2)$
-- statement:
--   **Number of zeros of a Hecke $L$-function in a window of bounded height.**
--
--   Let $F$ be a number field and let $\chi\colon C_F\to U(1)$ be a Hecke character, i.e. a continuous unitary character of the idele class group $C_F=\mathbb A_F^\times/F^\times$. Let
--   $$L(s,\chi)=\Gamma_F(s,\chi)\,L_f(s,\chi)$$
--   be the completed Hecke $L$-function: $L_f(s,\chi)$ is the finite Hecke $L$-function (the meromorphic continuation of the Euler product over the finite places) and $\Gamma_F(s,\chi)$ is the product of the Archimedean local factors. It is a meromorphic function on $\mathbb C$, entire unless $\chi=|\cdot|_F^{-it_0}$ for some real $t_0$, in which case its only poles are simple poles at $it_0$ and $1+it_0$; all its zeros lie in the critical strip $0<\operatorname{Re}(s)<1$. Write $\rho=\beta+i\gamma$ for the zeros of $L(s,\chi)$ and $m_\rho\ge1$ for their multiplicities.
--
--   There is a constant $C=C(F,\chi)$ such that for every real number $T$ the set of zeros $\rho$ with $|\gamma-T|\le1$ is finite and
--   $$\sum_{\rho\,:\ |\gamma-T|\le 1}m_\rho\ \le\ C\,\log(|T|+2).$$
--   In other words, the number of zeros, counted with multiplicity, whose ordinate lies in $[T-1,T+1]$ is $O(\log(|T|+2))$.
--
--   This is the basic local density estimate for the zeros of an $L$-function. It implies that the number of zeros with $|\gamma|\le T$ is $O(T\log T)$ for $T\ge2$, hence the absolute convergence of $\sum_\rho\Phi(\rho)$ for every $\Phi$ which decays rapidly on vertical strips, and it is the first step towards the partial fraction expansion of $L'/L$ and the choice of ordinates avoiding the zeros. In the source these are the facts, quoted from Lang's *Algebraic Number Theory*, Ch. XVII, behind the assertion of §B.4.2.1 that $L'(s,\chi)/L(s,\chi)$ has slow growth near its poles, which is what allows the Asymptotic Residue Theorem to be applied in the proof of the explicit formulas.
--
--   **Formalization Note.** $L(s,\chi)$ is `completedHeckeLFunction χ` (in meromorphic normal form). A zero is a point of positive meromorphic order, `0 < meromorphicOrderAt (completedHeckeLFunction χ) ρ`, and its multiplicity is that order (`untop₀` extracts the integer). The sum is a `finsum` over the set of zeros in the window; since a `finsum` over an infinite support is $0$ by convention, the finiteness of that set is asserted separately in the conclusion. The source cites the result without printing it; the statement is the standard one.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 614, §B.4.2.1, the sentence containing eq. (B.4.2.1) (the statement is cited there, not printed); classical reference: S. Lang, Algebraic Number Theory, Springer, Ch. XVII, Prop. 2.3, Cor. 2.5 and Prop. 2.7 (as cited by the paper)

import Definitions.Def_MasulloGRH_CompletedL

set_option autoImplicit false

namespace MasulloGRH

theorem completedHeckeLFunction_zeros_unit_window_le_log
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) :
    ∃ C : ℝ, ∀ T : ℝ,
      {ρ : ℂ | 0 < meromorphicOrderAt (completedHeckeLFunction χ) ρ ∧ |ρ.im - T| ≤ 1}.Finite ∧
      ∑ᶠ ρ ∈ {ρ : ℂ | 0 < meromorphicOrderAt (completedHeckeLFunction χ) ρ ∧ |ρ.im - T| ≤ 1},
          (((meromorphicOrderAt (completedHeckeLFunction χ) ρ).untop₀ : ℤ) : ℝ)
        ≤ C * Real.log (|T| + 2) := by sorry

end MasulloGRH
