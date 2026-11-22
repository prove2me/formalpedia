-- Prove2me | Theorems.Thm_MasulloGRH_adelicSchwartz_range_eval_eq_schwartzBruhat
-- name    : MasulloGRH.adelicSchwartz_range_eval_eq_schwartzBruhat
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T16:39:47.434867+00:00
-- url     : https://prove2.me/theorems/cc7a23b8-4827-4760-884e-95b12a2c4bff
-- title:
--   Lemma 2.1.3.2(2)–(3), corrected — $\mathcal S(\mathbb A_F)$ is the space of finite sums $\sum_if_{\infty,i}(x_\infty)\,h_i(x_f)$, $f_{\infty,i}$ Schwartz, $h_i$ locally constant of compact support
-- statement:
--   **Concrete description of the adelic Schwartz–Bruhat space** (Lemma 2.1.3.2(2)–(3) and Example 2.1.3.1 of the source).
--
--   Let $F$ be a number field with $r_1$ real and $r_2$ complex places, and write its adele ring as $\mathbb A_F=\mathbb A_{F,S_\infty}\times\mathbb A_F^f$, where $\mathbb A_{F,S_\infty}=\prod_{w\mid\infty}F_w\cong\mathbb R^{r_1}\times\mathbb C^{r_2}$ is the archimedean part and $\mathbb A_F^f$ is the ring of finite adeles; an adele is written $x=(x_\infty,x_f)$. Let $\mathcal S(\mathbb A_F)$ be the Schwartz–Bruhat space of the additive group of $\mathbb A_F$ in the sense of Bruhat: the union of the spaces $\mathcal S(\Gamma/k)$ over all pairs of an open compactly generated subgroup $\Gamma\subset\mathbb A_F$ and a good compact subgroup $k\subset\Gamma$.
--
--   Then a function $\varphi\colon\mathbb A_F\to\mathbb C$ belongs to $\mathcal S(\mathbb A_F)$ if and only if it is a finite sum
--   $$\varphi(x)=\sum_{i=1}^{r}f_{\infty,i}(x_\infty)\,h_i(x_f),$$
--   where each $f_{\infty,i}$ is a Schwartz function on the real vector space $\mathbb A_{F,S_\infty}\cong\mathbb R^{r_1}\times\mathbb C^{r_2}$ and each $h_i\colon\mathbb A_F^f\to\mathbb C$ is locally constant with compact support.
--
--   In other words the canonical linear map $\mathcal S(\mathbb A_{F,S_\infty})\otimes\mathcal S(\mathbb A_F^f)\to\mathcal S(\mathbb A_F)$ of (2.1.3.2) is onto, with $\mathcal S(\mathbb A_F^f)=C_c^\infty(\mathbb A_F^f)$. Since a locally constant function with compact support on $\mathbb A_F^f$ is a finite linear combination of indicator functions $\prod_v1_{a_v+\pi_v^{N_v}\mathcal O_{F_v}}$ (almost all factors being $1_{\mathcal O_{F_v}}$), this is the description of $\mathcal S(\mathbb A_F)$ as the restricted tensor product $\mathcal S(\mathbb A_{F,S_\infty})\otimes\bigotimes'_v\mathcal S(F_v)$ used in Tate's thesis.
--
--   The source uses this description in every argument about adelic $\theta$-functions and zeta integrals (for instance at the beginning of the proof of Lemma 2.2.2.1). On the platform it identifies the two existing models of $\mathcal S(\mathbb A_F)$, so that the results proved for the concrete model (Fourier inversion, Poisson summation, dilations) apply to Bruhat's space.
--
--   **Deviation from the source.** Part (3) of the printed lemma takes the non-archimedean factors to be indicator functions $\prod_v1_{K_v}$ of compact *subgroups* $K_v\subset F_v$. Such functions are even in every finite coordinate, so they do not span $\mathcal S(\mathbb A_F)$ (for $F=\mathbb Q$ the function with factor $1_{1+3\mathbb Z_3}$ at the prime $3$ is not reached). The correct statement, which is the one of Example 2.1.3.1 and the one used in the proof of Lemma 2.2.2.1 of the source, uses indicator functions of cosets $a_v+\pi_v^{N_v}\mathcal O_{F_v}$, i.e. arbitrary locally constant functions with compact support.
--
--   **Formalization Note.** The left-hand side is the set of functions `f.eval` for `f : MasulloGRH.AdelicSchwartz F`. The right-hand side is the platform submodule `NumberField.AdelicFourier.schwartzBruhat F` of `AdeleRing (𝓞 F) F → ℂ`: the $\mathbb C$-linear span of the functions $x\mapsto g(\rho(x_\infty))\,h(x_f)$, where $\rho$ is Mathlib's ring isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace` of $\mathbb A_{F,S_\infty}$ with $\mathbb R^{r_1}\times\mathbb C^{r_2}$, $g$ is a Mathlib Schwartz map on $\mathbb R^{r_1}\times\mathbb C^{r_2}$, and $h$ satisfies `IsLocallyConstant` and `HasCompactSupport`. Only the equality of function spaces is stated; the topological form of (2.1.3.2) is not part of this statement.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 68, Lemma 2.1.3.2, parts (2) and (3) (part (3) in the corrected form), eq. (2.1.3.2), with Example 2.1.3.1, pp. 67–68, eq. (2.1.3.1); classical reference cited there (p. 67, p. 69): F. Bruhat, Distributions sur un groupe localement compact et applications à l'étude des représentations des groupes $p$-adiques, Bulletin de la S.M.F., tome 89 (1961)

import Mathlib
import Definitions.Def_MasulloGRH_AdelicTheta
import Definitions.Def_NumberField_AdelicFourier

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem adelicSchwartz_range_eval_eq_schwartzBruhat
    (F : Type*) [Field F] [NumberField F] :
    Set.range (fun f : AdelicSchwartz F => f.eval) =
      (NumberField.AdelicFourier.schwartzBruhat F : Set (AdeleRing (𝓞 F) F → ℂ)) := by sorry

end MasulloGRH
