-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhatAverage_transfer
-- name    : MasulloGRH.schwartzBruhatAverage_transfer
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T14:38:23.745234+00:00
-- url     : https://prove2.me/theorems/43eac801-e10e-4500-8149-17aa46bda4f5
-- title:
--   Averaging over a structural pair maps $\mathcal S(\Gamma/k)$ continuously into $\mathcal S(\Gamma'/k')$
-- statement:
--   Let $G$ be a Hausdorff locally compact abelian group. Let $(\Gamma,k)$ and $(\Gamma',k')$ be two structural pairs of $G$, with presentations
--
--   $$
--   \pi\colon\Gamma\to E=\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F,\qquad \pi'\colon\Gamma'\to E'=\mathbb R^{m'}\times\mathbb T^{n'}\times\mathbb Z^{r'}\times F'
--   $$
--
--   of $\Gamma/k$ and $\Gamma'/k'$ as elementary abelian Lie groups (continuous, open, surjective homomorphisms with kernels $k$ and $k'$). For $g\in\mathcal S(E)$, let $\iota_{\Gamma,k}(g)$ be the function on $G$ equal to $g\circ\pi$ on $\Gamma$ and $0$ off $\Gamma$. For $f\colon G\to\mathbb C$, let
--
--   $$
--   (A_{\Gamma',k'}f)(x)=\mathbf 1_{\Gamma'}(x)\int_{k'}f(xy)\,d\mu_{k'}(y),
--   $$
--
--   where $\mu_{k'}$ is the normalized Haar measure of the compact group $k'$. Then there is a **continuous** linear map $T\colon\mathcal S(E)\to\mathcal S(E')$ such that
--
--   $$
--   A_{\Gamma',k'}\bigl(\iota_{\Gamma,k}(g)\bigr)=\iota_{\Gamma',k'}\bigl(T g\bigr)\qquad\text{for all } g\in\mathcal S(E).
--   $$
--
--   In words: averaging a function from $\mathcal S(k,\Gamma)$ over $k'$ and cutting it off to $\Gamma'$ gives a function in $\mathcal S(k',\Gamma')$, and this depends continuously on the input. This is the analytic input in the averaging operators of the proof of Theorem D.1.5.7. It combines the averaging map of Theorem D.1.7.1, which lands continuously in $\mathcal S(G/k')$ via Lemma D.1.6.18 for elementary abelian groups, with pullback and extension by zero along open subgroups (Lemma D.1.5.4).
--
--   **Formalization Note** $\mathcal S(E)$ carries the topology of the seminorms $\sup|a|^j|x|^i\|D^kg\|$ (Definition D.1.3.1). $A_{\Gamma',k'}$ is `schwartzBruhatAverage` from `Def_MasulloGRH_SchwartzBruhatAveraging`, and $\iota_{\Gamma,k}$ is `extendPullback Γ π`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Lemma D.1.5.4 (p. 762), Lemma D.1.6.18 (p. 772), Theorem D.1.7.1 and its proof (pp. 776–777), as used for the averaging operators in the proof of Theorem D.1.5.7 (pp. 760–764); F. Bruhat, Distributions sur un groupe localement compact, Bull. SMF 89 (1961), §9

import Definitions.Def_MasulloGRH_SchwartzBruhatAveraging

set_option autoImplicit false

namespace MasulloGRH

theorem schwartzBruhatAverage_transfer
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G]
    (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π)
    (Γ' k' : Subgroup G) (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
    (π' : ↥Γ' →* Multiplicative (ElemGroup m' n' r' s' d')) (hs' : IsStructuralPair Γ' k')
    (hπ' : IsElemPresentation Γ' k' π') :
    ∃ T : ElemSchwartz m n r s d →ₗ[ℂ] ElemSchwartz m' n' r' s' d', Continuous T ∧
      ∀ g : ElemSchwartz m n r s d,
        schwartzBruhatAverage Γ' k' (extendPullback Γ π g.toFun) =
          extendPullback Γ' π' (T g).toFun := by
  sorry

end MasulloGRH
