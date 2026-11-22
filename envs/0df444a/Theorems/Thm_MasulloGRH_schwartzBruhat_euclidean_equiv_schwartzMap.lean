-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhat_euclidean_equiv_schwartzMap
-- name    : MasulloGRH.schwartzBruhat_euclidean_equiv_schwartzMap
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T16:39:32.868371+00:00
-- url     : https://prove2.me/theorems/151b37c7-fdaa-4e10-9a58-c1650f675356
-- title:
--   §2.1.1.3 — for a finite-dimensional real vector space $E$, Bruhat's space $\mathcal S(E)$ is the classical Schwartz space, as topological vector spaces
-- statement:
--   **On a real vector space the Schwartz–Bruhat space is the Schwartz space** (§2.1.1.3 of the source).
--
--   Let $E$ be a finite-dimensional real normed vector space (for instance $\mathbb R^m$, or the archimedean part $\mathbb A_{F,S_\infty}\cong\mathbb R^{r_1}\times\mathbb C^{r_2}$ of the adeles of a number field). Let $\mathcal S_{\mathrm{Br}}(E)$ be the Schwartz–Bruhat space of the additive group of $E$ in the sense of Bruhat, with its locally convex inductive limit topology, and let $\mathcal S(E)$ be the classical Schwartz space of smooth functions $f\colon E\to\mathbb C$ all of whose derivatives decay faster than every power of $\|x\|^{-1}$ (Definition 2.1.1.4 of the source), with the Fréchet topology of the seminorms $\sup_x\|x\|^k\|D^nf(x)\|$.
--
--   Then the two spaces coincide, as function spaces and as topological vector spaces: there is a $\mathbb C$-linear homeomorphism
--   $$T\colon\mathcal S_{\mathrm{Br}}(E)\ \xrightarrow{\ \sim\ }\ \mathcal S(E),\qquad (Tf)(x)=f(x)\quad(x\in E).$$
--
--   In particular a function on $E$ is a Schwartz–Bruhat function if and only if it is a Schwartz function.
--
--   The source records this for $G=\mathbb R$; it is the archimedean ingredient of the description $\mathcal S(\mathbb A_F)=\mathcal S(\mathbb A_{F,S_\infty})\otimes\mathcal S(\mathbb A_F^f)$, and it transfers Mathlib's theory of `SchwartzMap` (Fourier transform, seminorms, density) to the platform's Schwartz–Bruhat spaces.
--
--   **Formalization Note.** $\mathcal S_{\mathrm{Br}}(E)$ is the platform space `MasulloGRH.SchwartzBruhat (Multiplicative E)` (groups are written multiplicatively there) and $\mathcal S(E)$ is Mathlib's `SchwartzMap E ℂ`. The statement asserts the existence of a continuous linear equivalence `T` with `T f x = f (Multiplicative.ofAdd x)`; since `T f` is determined by this formula, `T` is unique. The source states the case $E=\mathbb R$; the general finite-dimensional case is the same statement for the elementary group $\mathbb R^m$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 62–63, §2.1.1.3 (the Schwartz–Bruhat space of an elementary group, and "for $G=\mathbf R$ the classical Schwartz space $\mathcal S(\mathbf R)$ is recovered"), with Definition 2.1.1.4, pp. 60–61; classical reference cited there: F. Bruhat, Distributions sur un groupe localement compact et applications à l'étude des représentations des groupes $p$-adiques, Bulletin de la S.M.F., tome 89 (1961), §9

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem schwartzBruhat_euclidean_equiv_schwartzMap
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    ∃ T : SchwartzBruhat (Multiplicative E) ≃L[ℂ] SchwartzMap E ℂ,
      ∀ (f : SchwartzBruhat (Multiplicative E)) (x : E),
        T f x = f (Multiplicative.ofAdd x) := by sorry

end MasulloGRH
