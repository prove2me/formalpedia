-- Prove2me | Theorems.Thm_MasulloGRH_completedHeckeLFunction_logDeriv_local_partial_fraction
-- name    : MasulloGRH.completedHeckeLFunction_logDeriv_local_partial_fraction
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:32:14.187122+00:00
-- url     : https://prove2.me/theorems/90c918ce-4393-4a8a-b672-4d3e6fa6dcb9
-- title:
--   Local partial fractions for a Hecke $L$-function: $\frac{L'}{L}(s,\chi)=\sum_{|\gamma-t|\le1}\frac{m_\rho}{s-\rho}+O(\log|t|)$ for $-1\le\sigma\le2$
-- statement:
--   **Local partial fraction expansion of the logarithmic derivative of a Hecke $L$-function.**
--
--   Let $F$ be a number field and let $\chi\colon C_F\to U(1)$ be a Hecke character, i.e. a continuous unitary character of the idele class group $C_F=\mathbb A_F^\times/F^\times$. Let
--   $$L(s,\chi)=\Gamma_F(s,\chi)\,L_f(s,\chi)$$
--   be the completed Hecke $L$-function: $L_f(s,\chi)$ is the finite Hecke $L$-function (the meromorphic continuation of the Euler product over the finite places) and $\Gamma_F(s,\chi)$ is the product of the Archimedean local factors. It is a meromorphic function on $\mathbb C$, entire unless $\chi=|\cdot|_F^{-it_0}$ for some real $t_0$, in which case its only poles are simple poles at $it_0$ and $1+it_0$; all its zeros lie in the critical strip $0<\operatorname{Re}(s)<1$. Write $\rho=\beta+i\gamma$ for the zeros of $L(s,\chi)$ and $m_\rho\ge1$ for their multiplicities.
--
--   There are constants $C=C(F,\chi)$ and $T_0=T_0(F,\chi)\ge2$ such that for every $s=\sigma+it$ with
--   $$-1\le\sigma\le2,\qquad|t|\ge T_0,\qquad L(s,\chi)\neq0,$$
--   one has
--   $$\left|\frac{L'}{L}(s,\chi)-\sum_{\rho\,:\ |\gamma-t|\le1}\frac{m_\rho}{s-\rho}\right|\ \le\ C\,\log|t| .$$
--   The sum runs over the finitely many zeros whose ordinate is within $1$ of $t$.
--
--   So, up to an error of size $\log|t|$, the logarithmic derivative is governed near the critical strip by the zeros at distance $O(1)$. It is the standard tool for bounding $L'/L$ on suitable horizontal lines; in the source it is part of the input, quoted from Lang's *Algebraic Number Theory*, Ch. XVII, for the assertion of §B.4.2.1 that $L'(s,\chi)/L(s,\chi)$ has slow growth near its poles.
--
--   **Formalization Note.** $L(s,\chi)$ is `completedHeckeLFunction χ` (in meromorphic normal form), $L'/L$ is `logDeriv (completedHeckeLFunction χ)`, zeros are the points of positive `meromorphicOrderAt` and $m_\rho$ is that order. Since the function is in normal form, the hypothesis `completedHeckeLFunction χ s ≠ 0` excludes the zeros (and the poles, which do not occur for $|t|\ge T_0$ once $T_0$ is large). The sum is a `finsum`; its index set is finite because the zeros lie in the critical strip. The restriction $|t|\ge T_0$ keeps $s$ away from the two possible poles of $L(s,\chi)$ and makes $\log|t|\ge\log2>0$. The source cites the result without printing it; the statement is the standard one.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 614, §B.4.2.1, the sentence containing eq. (B.4.2.1) (the statement is cited there, not printed); classical reference: S. Lang, Algebraic Number Theory, Springer, Ch. XVII, Prop. 2.3, Cor. 2.5 and Prop. 2.7 (as cited by the paper)

import Definitions.Def_MasulloGRH_CompletedL

set_option autoImplicit false

namespace MasulloGRH

theorem completedHeckeLFunction_logDeriv_local_partial_fraction
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) :
    ∃ C T₀ : ℝ, 2 ≤ T₀ ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → T₀ ≤ |s.im| →
      completedHeckeLFunction χ s ≠ 0 →
      ‖logDeriv (completedHeckeLFunction χ) s -
          ∑ᶠ ρ ∈ {ρ : ℂ | 0 < meromorphicOrderAt (completedHeckeLFunction χ) ρ ∧
              |ρ.im - s.im| ≤ 1},
            (((meromorphicOrderAt (completedHeckeLFunction χ) ρ).untop₀ : ℤ) : ℂ) / (s - ρ)‖
        ≤ C * Real.log |s.im| := by sorry

end MasulloGRH
