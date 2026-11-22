-- Prove2me | Theorems.Thm_MasulloGRH_completedHeckeLFunction_logDeriv_bound_on_good_heights
-- name    : MasulloGRH.completedHeckeLFunction_logDeriv_bound_on_good_heights
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:31:55.222299+00:00
-- url     : https://prove2.me/theorems/bf99a4a4-a459-4727-90d6-bd378afd8d9e
-- title:
--   Good ordinates for a Hecke $L$-function: for every $m\in\mathbb Z$ there is $T\in[m,m+1]$ with $\frac{L'}{L}(\sigma+iT,\chi)\ll\log^2(|m|+2)$ uniformly for $-1\le\sigma\le2$
-- statement:
--   **Ordinates on which the logarithmic derivative of a Hecke $L$-function is small.**
--
--   Let $F$ be a number field and let $\chi\colon C_F\to U(1)$ be a Hecke character, i.e. a continuous unitary character of the idele class group $C_F=\mathbb A_F^\times/F^\times$. Let
--   $$L(s,\chi)=\Gamma_F(s,\chi)\,L_f(s,\chi)$$
--   be the completed Hecke $L$-function: $L_f(s,\chi)$ is the finite Hecke $L$-function (the meromorphic continuation of the Euler product over the finite places) and $\Gamma_F(s,\chi)$ is the product of the Archimedean local factors. It is a meromorphic function on $\mathbb C$, entire unless $\chi=|\cdot|_F^{-it_0}$ for some real $t_0$, in which case its only poles are simple poles at $it_0$ and $1+it_0$; all its zeros lie in the critical strip $0<\operatorname{Re}(s)<1$. Write $\rho=\beta+i\gamma$ for the zeros of $L(s,\chi)$ and $m_\rho\ge1$ for their multiplicities.
--
--   There is a constant $C=C(F,\chi)$ such that for every integer $m$ there is a real number $T_m$ with $m\le T_m\le m+1$ such that, for every real $\sigma$ with $-1\le\sigma\le2$, the function $L(s,\chi)$ is holomorphic and non-zero at $\sigma+iT_m$ and
--   $$\left|\frac{L'}{L}(\sigma+iT_m,\chi)\right|\ \le\ C\,\log^2(|m|+2).$$
--
--   Thus every horizontal strip $m\le\operatorname{Im}(s)\le m+1$ with $m\in\mathbb Z$ contains a horizontal segment, crossing the critical strip from $\operatorname{Re}(s)=-1$ to $\operatorname{Re}(s)=2$, which avoids the zeros and poles of $L(s,\chi)$ and on which $L'/L$ grows at most like the square of the logarithm of the height. Such segments are the horizontal sides of the rectangles used in contour integration of $\Phi(s)L'(s,\chi)/L(s,\chi)$, and this is the classical form of the assertion of §B.4.2.1 that $f(s)=L'(s,\chi)/L(s,\chi)$ "has slow growth near its poles" on the strips $\{1-a<\operatorname{Re}(s)<a\}$, $1<a\le2$ (Definition B.3.1.1): the heights $T_m$ tend to $\pm\infty$ linearly in $m$ and $f$ is polynomially bounded in $m$ on the corresponding segments.
--
--   **Deviation from the source.** Read literally, the assertion of §B.4.2.1 is not correct: as printed, Definition B.3.1.1 also imposes the bound at $k=0$ and is satisfied only by the zero function, and the contour lemma B.3.1.2 needs a lower bound on the heights $|T_k|$ (errata of the upstream formalization, items F17 and F33). What the cited results of Lang provide, and what is formalized here, is the classical existence of good ordinates in every interval $[m,m+1]$.
--
--   **Formalization Note.** $L(s,\chi)$ is `completedHeckeLFunction χ` (in meromorphic normal form) and $L'/L$ is `logDeriv (completedHeckeLFunction χ)`. Holomorphy and non-vanishing at the points of the segment are asserted explicitly (`AnalyticAt` and `≠ 0`), so that the bounded quantity is the genuine logarithmic derivative and not a junk value at a pole. The source cites the result without printing it; the statement is the standard one, and it does not use the source's Definition B.3.1.1.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 614, §B.4.2.1, the sentence containing eq. (B.4.2.1) (the statement is cited there, not printed); classical reference: S. Lang, Algebraic Number Theory, Springer, Ch. XVII, Prop. 2.3, Cor. 2.5 and Prop. 2.7 (as cited by the paper)

import Definitions.Def_MasulloGRH_CompletedL

set_option autoImplicit false

namespace MasulloGRH

theorem completedHeckeLFunction_logDeriv_bound_on_good_heights
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) :
    ∃ C : ℝ, ∀ m : ℤ, ∃ T : ℝ, (m : ℝ) ≤ T ∧ T ≤ m + 1 ∧
      ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
        AnalyticAt ℂ (completedHeckeLFunction χ) (σ + T * Complex.I) ∧
        completedHeckeLFunction χ (σ + T * Complex.I) ≠ 0 ∧
        ‖logDeriv (completedHeckeLFunction χ) (σ + T * Complex.I)‖
          ≤ C * Real.log (|(m : ℝ)| + 2) ^ 2 := by sorry

end MasulloGRH
