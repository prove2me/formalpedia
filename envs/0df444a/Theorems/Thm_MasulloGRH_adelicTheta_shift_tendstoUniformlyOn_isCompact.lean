-- Prove2me | Theorems.Thm_MasulloGRH_adelicTheta_shift_tendstoUniformlyOn_isCompact
-- name    : MasulloGRH.adelicTheta_shift_tendstoUniformlyOn_isCompact
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T16:39:27.552989+00:00
-- url     : https://prove2.me/theorems/b1cd0f9b-2b6a-420a-bdc7-fb8bd1a66978
-- title:
--   Lemma 2.2.2.1(1) — $\Psi_F(f)(g,x)=\sum_{\xi\in F^\times}f(g(\xi+x))$ converges absolutely and uniformly on compact subsets of $\mathrm{GL}_1(\mathbb A_F)\times\mathbb A_F$ and is continuous
-- statement:
--   **Locally uniform convergence of adelic theta series** (Lemma 2.2.2.1, first assertion and part (1), of the source).
--
--   Let $F$ be a number field, $\mathbb A_F$ its adele ring, $\mathrm{GL}_1(\mathbb A_F)$ its idele group with the idelic topology, and $f\in\mathcal S(\mathbb A_F)$ a Schwartz–Bruhat function. For an idele $g$ and an adele $x$ consider the series
--   $$\Psi_F(f)(g,x)=\sum_{\xi\in F^\times}f\big(g(\xi+x)\big),$$
--   where $F^\times$ is embedded diagonally in $\mathbb A_F$.
--
--   Then:
--
--   1. for every $(g,x)\in\mathrm{GL}_1(\mathbb A_F)\times\mathbb A_F$ the series converges absolutely, $\sum_{\xi\in F^\times}|f(g(\xi+x))|<\infty$;
--   2. the convergence is uniform on compact sets: for every compact subset $Z\subset\mathrm{GL}_1(\mathbb A_F)\times\mathbb A_F$ the partial sums $\sum_{\xi\in s}|f(g(\xi+x))|$, over finite subsets $s\subset F^\times$, converge to $\sum_{\xi\in F^\times}|f(g(\xi+x))|$ uniformly for $(g,x)\in Z$;
--   3. $\Psi_F(f)$ is a continuous function on $\mathrm{GL}_1(\mathbb A_F)\times\mathbb A_F$;
--   4. the completed sum is periodic under $F$ in the variable $x$: for all $\eta\in F$,
--   $$\Psi_F(f)(g,x+\eta)+f\big(g(x+\eta)\big)=\Psi_F(f)(g,x)+f(gx).$$
--
--   For $x=0$ the function $g\mapsto\Psi_F(f)(g,0)=\sum_{\xi\in F^\times}f(\xi g)$ is the global adelic $\theta$-function $\Phi_F(f)$ of Definition 2.2.3.1, and item 3 gives its continuity on the idele group. The left-hand side of item 4 is the full theta series $\sum_{\xi\in F}f(g(\xi+x))$, a continuous function on $\mathrm{GL}_1(\mathbb A_F)\times\mathbb A_F/F$. This is the convergence statement on which the adelic Poisson summation formula and the Riemann–Roch theorem of Tate's thesis rest.
--
--   **Formalization Note.** $f$ is an element of the platform space `MasulloGRH.AdelicSchwartz F` and `f.eval` its underlying function. Item 2 is `TendstoUniformlyOn` for the net of finite partial sums of the series of absolute values, indexed by `Finset Fˣ`, i.e. unconditional uniform convergence. Part (2) of the source lemma (invariance of $\Psi_F(f)(g,0)$ under $F^\times$) is a reindexing of the sum and is not restated; part (3) is not included (it does not hold as printed beyond the chosen representatives).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 77, Lemma 2.2.2.1 (Averaging over $F^\times$-orbits), first assertion and part (1), eq. (2.2.2.1); classical reference cited there: D. Ramakrishnan, R. J. Valenza, Fourier Analysis on Number Fields, Springer, Ch. 7, §7.2, Lemma 7.6

import Mathlib
import Definitions.Def_MasulloGRH_AdelicTheta

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem adelicTheta_shift_tendstoUniformlyOn_isCompact
    (F : Type*) [Field F] [NumberField F] (f : AdelicSchwartz F) :
    (∀ p : IdeleGroup F × AdeleRing (𝓞 F) F,
      Summable (fun ξ : Fˣ =>
        ‖f.eval ((p.1 : AdeleRing (𝓞 F) F) *
          (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) + p.2))‖)) ∧
    (∀ Z : Set (IdeleGroup F × AdeleRing (𝓞 F) F), IsCompact Z →
      TendstoUniformlyOn
        (fun (s : Finset Fˣ) (p : IdeleGroup F × AdeleRing (𝓞 F) F) =>
          ∑ ξ ∈ s, ‖f.eval ((p.1 : AdeleRing (𝓞 F) F) *
            (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) + p.2))‖)
        (fun p : IdeleGroup F × AdeleRing (𝓞 F) F =>
          ∑' ξ : Fˣ, ‖f.eval ((p.1 : AdeleRing (𝓞 F) F) *
            (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) + p.2))‖)
        Filter.atTop Z) ∧
    Continuous (fun p : IdeleGroup F × AdeleRing (𝓞 F) F =>
      ∑' ξ : Fˣ, f.eval ((p.1 : AdeleRing (𝓞 F) F) *
        (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) + p.2))) ∧
    ∀ (g : IdeleGroup F) (x : AdeleRing (𝓞 F) F) (η : F),
      (∑' ξ : Fˣ, f.eval ((g : AdeleRing (𝓞 F) F) *
          (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) +
            (x + algebraMap F (AdeleRing (𝓞 F) F) η)))) +
        f.eval ((g : AdeleRing (𝓞 F) F) * (x + algebraMap F (AdeleRing (𝓞 F) F) η)) =
      (∑' ξ : Fˣ, f.eval ((g : AdeleRing (𝓞 F) F) *
          (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) + x))) +
        f.eval ((g : AdeleRing (𝓞 F) F) * x) := by sorry

end MasulloGRH
