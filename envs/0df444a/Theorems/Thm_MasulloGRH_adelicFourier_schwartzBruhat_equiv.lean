-- Prove2me | Theorems.Thm_MasulloGRH_adelicFourier_schwartzBruhat_equiv
-- name    : MasulloGRH.adelicFourier_schwartzBruhat_equiv
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T16:39:32.20136+00:00
-- url     : https://prove2.me/theorems/d99d205d-ec65-4cd7-bf38-6d8bf2576003
-- title:
--   Theorem 2.2.3.2 (set-up) — the adelic Fourier transform is a linear topological automorphism of $\mathcal S(\mathbb A_F)$, with $\widehat{\widehat f}(x)=f(-x)$
-- statement:
--   **The adelic Fourier transform on the Schwartz–Bruhat space** (the set-up of Theorem 2.2.3.2 of the source).
--
--   Let $F$ be a number field, $\mathbb A_F$ its adele ring, $\nu$ the additive Tamagawa measure on $\mathbb A_F$ (the Haar measure with $\bar\nu(\mathbb A_F/F)=1$), $\psi=\psi_{F,\mathrm{std}}$ the standard additive character of $\mathbb A_F$, and $\mathcal S(\mathbb A_F)$ the Schwartz–Bruhat space of $\mathbb A_F$ with its locally convex inductive limit topology. For $f\in\mathcal S(\mathbb A_F)$ the adelic Fourier transform is
--   $$\widehat f(y)=\int_{\mathbb A_F}f(x)\,\psi(xy)\,d\nu(x)\qquad(y\in\mathbb A_F).$$
--
--   Then:
--
--   1. every $f\in\mathcal S(\mathbb A_F)$ is $\nu$-integrable, so the integral converges absolutely;
--   2. $\widehat f$ is again a Schwartz–Bruhat function, and $f\mapsto\widehat f$ is a $\mathbb C$-linear homeomorphism of $\mathcal S(\mathbb A_F)$ onto itself;
--   3. Fourier inversion holds without a normalizing constant: $\widehat{\widehat f}(x)=f(-x)$ for all $x\in\mathbb A_F$.
--
--   Item 3 expresses that $\nu$ is self-dual for $\psi$. The statement is the adelic case of Bruhat's theorem that the Fourier transform is a topological isomorphism $\mathcal S(G)\to\mathcal S(\widehat G)$ for a locally compact abelian group $G$, combined with the self-duality $\mathbb A_F\cong\widehat{\mathbb A_F}$, $y\mapsto\psi(\,\cdot\,y)$, of Tate's thesis. It is what gives a meaning to the right-hand side $|g|_F^{-1}\Phi_F(\widehat f)(g^{-1})+|g|_F^{-1}\widehat f(0)-f(0)$ of the adelic Riemann–Roch theorem as a statement about $\theta$-functions of Schwartz–Bruhat functions, to the continuous functional $\widehat\delta_0(f)=\widehat f(0)$ of Definition 2.2.4.4, and to the dual side $Z(\widehat f,\widehat c)$ of the functional equation of the global zeta integrals.
--
--   **Formalization Note.** The automorphism is a continuous linear equivalence `T` of the platform space `MasulloGRH.AdelicSchwartz F` whose underlying function is the integral above, `(T f).eval = MasulloGRH.adelicFourier f`; inversion is stated as `(T (T f)).eval x = f.eval (-x)`. The source uses these facts without a numbered statement; the standard character is taken in the sign convention of Tate's thesis (the convention of the platform definition), for which the adelic Riemann–Roch theorem holds.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 82, Theorem 2.2.3.2 and Remark 2.2.3.3 (the global Fourier transform $f\mapsto\widehat f$ on $\mathcal S(\mathbf A_F)$), p. 91, Definition 2.2.4.4 (the functional $\widehat\delta_0$), and p. 558, Example A.3.1.9; classical references cited there: J.W.S. Cassels, A. Fröhlich, Algebraic Number Theory, London Mathematical Society, 2010, Ch. XV, §4.1, Thm. 4.1.2 (self-duality of the measure); F. Bruhat, Distributions sur un groupe localement compact et applications à l'étude des représentations des groupes $p$-adiques, Bulletin de la S.M.F., tome 89 (1961) (the Schwartz–Bruhat space)

import Mathlib
import Definitions.Def_MasulloGRH_AdelicTheta

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem adelicFourier_schwartzBruhat_equiv
    (F : Type*) [Field F] [NumberField F] :
    (∀ f : AdelicSchwartz F, Integrable f.eval tamagawaAdelic) ∧
    ∃ T : AdelicSchwartz F ≃L[ℂ] AdelicSchwartz F,
      (∀ f : AdelicSchwartz F, (T f).eval = adelicFourier f) ∧
      ∀ (f : AdelicSchwartz F) (x : AdeleRing (𝓞 F) F), (T (T f)).eval x = f.eval (-x) := by sorry

end MasulloGRH
