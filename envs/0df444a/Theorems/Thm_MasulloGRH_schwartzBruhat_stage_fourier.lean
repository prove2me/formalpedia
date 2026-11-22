-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhat_stage_fourier
-- name    : MasulloGRH.schwartzBruhat_stage_fourier
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T19:05:45.096835+00:00
-- url     : https://prove2.me/theorems/a8671522-c796-4860-a529-c60c077c076b
-- title:
--   Lemma D.1.6.19(2), stage form — the Fourier transform maps $\mathcal S(k,\Gamma)$ continuously into $\mathcal S(\Gamma^\perp,k^\perp)$
-- statement:
--   **Fourier transform of a Schwartz–Bruhat stage** (auxiliary lemma for Lemma D.1.6.19(2)): the Fourier transform maps the stage $\mathcal S(k,\Gamma)$ of $\mathcal S(G)$ continuously into the stage $\mathcal S(\Gamma^\perp,k^\perp)$ of $\mathcal S(\widehat G)$.
--
--   Let $G$ be a Hausdorff locally compact abelian group, written multiplicatively, with a regular Haar measure $\mu$ on its Borel $\sigma$-algebra, and let $\widehat G$ be its Pontryagin dual (continuous characters $\chi\colon G\to U(1)$, compact-open topology). For a subgroup $H\subseteq G$ write $H^\perp=\{\chi\in\widehat G:\chi|_H=1\}$ for its annihilator. Let $(\Gamma,k)$ be a structural pair of $G$ (Definition D.1.5.1: $\Gamma$ open and compactly generated, $k\subseteq\Gamma$ a good subgroup, i.e. closed with $k^\perp$ open and compactly generated), and let
--   $$\pi\colon\Gamma\longrightarrow E=\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times\textstyle\prod_{i<s}\mathbb Z/d_i\qquad(d_i\neq0)$$
--   be a presentation of $\Gamma/k$: a continuous, open, surjective homomorphism with kernel $k$. For $g$ in the elementary Schwartz–Bruhat space $\mathcal S(E)$ (Definition D.1.3.1) let $f_g\colon G\to\mathbb C$ be the function equal to $g\circ\pi$ on $\Gamma$ and to $0$ off $\Gamma$; these functions form the stage $\mathcal S(k,\Gamma)$ of $\mathcal S(G)$. Recall (Lemma D.1.5.2(2)) that $(k^\perp,\Gamma^\perp)$ is then a structural pair of $\widehat G$.
--
--   **Statement.** There are a presentation
--   $$\pi'\colon k^\perp\longrightarrow E'=\mathbb R^{m'}\times\mathbb T^{n'}\times\mathbb Z^{r'}\times\textstyle\prod_{i<s'}\mathbb Z/d'_i$$
--   of $k^\perp/\Gamma^\perp$ (continuous, open, surjective, kernel $\Gamma^\perp$, all $d'_i\neq0$) and a continuous linear map $T\colon\mathcal S(E)\to\mathcal S(E')$ such that for every $g\in\mathcal S(E)$:
--   1. $f_g$ is $\mu$-integrable;
--   2. its Fourier transform $\widehat{f_g}(\chi)=\int_G f_g(x)\,\overline{\chi(x)}\,d\mu(x)$ is the function on $\widehat G$ equal to $(Tg)\circ\pi'$ on $k^\perp$ and to $0$ off $k^\perp$:
--   $$\widehat{f_g}(\chi)=\begin{cases}(Tg)(\pi'(\chi)),&\chi\in k^\perp,\\ 0,&\chi\notin k^\perp.\end{cases}$$
--
--   Classically one may take $E'=\mathbb R^m\times\mathbb T^r\times\mathbb Z^n\times\prod_i\mathbb Z/d_i\cong\widehat E$, with $\pi'$ the composite $k^\perp\to\widehat{\Gamma/k}\cong\widehat E$ of restriction of characters to $\Gamma$; then $T$ is, up to the positive constant comparing the image of $\mu|_\Gamma$ with the standard Haar measure of $E$, the Fourier transform $\mathcal S(E)\to\mathcal S(\widehat E)$ of the elementary group $E$ (Schwartz functions on $\mathbb R^m$ to Schwartz functions, smooth functions on $\mathbb T^n$ to rapidly decreasing sequences on $\mathbb Z^n$, rapidly decreasing sequences on $\mathbb Z^r$ to smooth functions on $\mathbb T^r$). This is the stage-level content of Lemma D.1.6.19(2), whose proof identifies $\mathcal F_G$ with the direct limit of the Fourier transforms of the stages; together with Fourier inversion and Pontryagin duality it yields that the Fourier transform is a linear topological isomorphism $\mathcal S(G)\to\mathcal S(\widehat G)$ of the locally convex inductive limits.
--
--   **Formalization Note.** Structural pairs, presentations, the elementary spaces `ElemSchwartz m n r s d` (with their Fréchet topology) and the extension-by-zero pull-back `extendPullback Γ π g` are those of the platform definition `MasulloGRH_SchwartzBruhat`; the annihilators are `LCAGroup.annihilator` (platform definition `LCAGroup_Annihilator`), and the Fourier transform is `RiemannMasullo.lcaFourier μ f χ = ∫ x, f x * star (χ x) ∂μ`. The second assertion is an equality of functions on $\widehat G$ (for every $\chi$, not almost everywhere). Only "into, continuously" is asserted (not that $T$ is an isomorphism).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 773, Lemma D.1.6.19(2) (stage-level form: the Fourier transform maps S(k,Γ) into S(Γ^⊥,k^⊥)); auxiliary lemma for the proof of Lemma D.1.6.19(2) (MasulloGRH.schwartzBruhat_fourier_equiv); classical reference: F. Bruhat, Distributions sur un groupe localement compact et applications à l'étude des représentations des groupes p-adiques, Bull. Soc. Math. France 89 (1961); M. S. Osborne, On the Schwartz–Bruhat space and the Paley–Wiener theorem for locally compact abelian groups, J. Funct. Anal. 19 (1975), 40–49

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Definitions.Def_RiemannMasullo_LCAFourierConvolution
import Definitions.Def_LCAGroup_Annihilator

open MeasureTheory Topology

set_option autoImplicit false

namespace MasulloGRH

theorem schwartzBruhat_stage_fourier
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d))
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) :
    ∃ (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
      (π' : ↥(LCAGroup.annihilator k) →* Multiplicative (ElemGroup m' n' r' s' d'))
      (T : ElemSchwartz m n r s d →ₗ[ℂ] ElemSchwartz m' n' r' s' d'),
      IsElemPresentation (LCAGroup.annihilator k) (LCAGroup.annihilator Γ) π' ∧ Continuous T ∧
      ∀ g : ElemSchwartz m n r s d,
        Integrable (extendPullback Γ π g.toFun) μ ∧
          RiemannMasullo.lcaFourier μ (extendPullback Γ π g.toFun) =
            extendPullback (LCAGroup.annihilator k) π' (T g).toFun := by sorry

end MasulloGRH
