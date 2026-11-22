-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhat_averaging
-- name    : MasulloGRH.schwartzBruhat_averaging
-- status  : Proved
-- author  : @Miikka
-- created : 2026-11-21T13:44:04.081676+00:00
-- url     : https://prove2.me/theorems/3baa60ef-ec32-427f-89af-2d1580810d6b
-- title:
--   Averaging operators on Schwartz–Bruhat spaces
-- statement:
--   Let $G$ be a Hausdorff locally compact abelian group with Schwartz–Bruhat space $\mathcal S(G)$, and for a structural pair $(\Gamma,k)$ with a presentation $\Gamma/k\cong E$ (an elementary abelian Lie group $\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$) write $\iota_{\Gamma,k}\colon\mathcal S(E)\to\mathcal S(G)$ for the inclusion of the functions supported on $\Gamma$ and invariant under $k$.
--
--   Then there are linear operators $A_{\Gamma,k}\colon\mathcal S(G)\to\mathcal S(G)$, one for each structural pair, namely the averaging operators
--   $$(A_{\Gamma,k}f)(x)=\mathbf 1_\Gamma(x)\int_k f(xy)\,dy\qquad(dy \text{ the normalized Haar measure of the compact group } k),$$
--   with the following properties.
--
--   1. $A_{\Gamma,k}$ takes values in $\iota_{\Gamma,k}(\mathcal S(\Gamma/k))$, for every presentation of $\Gamma/k$.
--   2. If $(\Gamma,k)$ and $(\Gamma',k')$ are structural with $\Gamma\subseteq\Gamma'$ and $k'\subseteq k$, then $A_{\Gamma',k'}$ is the identity on $\iota_{\Gamma,k}(\mathcal S(\Gamma/k))$, and $A_{\Gamma,k}\circ A_{\Gamma',k'}=A_{\Gamma,k}$.
--   3. For any two structural pairs $(\Gamma,k)$, $(\Gamma',k')$ with presentations, $A_{\Gamma',k'}\circ\iota_{\Gamma,k}=\iota_{\Gamma',k'}\circ T$ for a *continuous* linear map $T\colon\mathcal S(\Gamma/k)\to\mathcal S(\Gamma'/k')$.
--
--   These operators make the spaces $\mathcal S(\Gamma/k)$ into a directed system with compatible continuous projections.
--
--   **Formalization Note** The formal statement asserts the existence of a family $A$ indexed by all pairs of subgroups (its values on non-structural pairs are irrelevant) with properties 1–3; the displayed formula is the intended construction.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.1.5, proof of Theorem D.1.5.7, pp. 760–764 (and F. Bruhat, Distributions sur un groupe localement compact, Bull. SMF 89 (1961))

import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

namespace MasulloGRH

theorem schwartzBruhat_averaging
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] :
    ∃ A : Subgroup G → Subgroup G → (SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat G),
      (∀ (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
        (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
        (hπ : IsElemPresentation Γ k π) (f : SchwartzBruhat G),
        ∃ g, A Γ k f = SchwartzBruhat.ofElem Γ k π hs hπ g) ∧
      (∀ (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
        (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
        (hπ : IsElemPresentation Γ k π) (Γ' k' : Subgroup G), IsStructuralPair Γ' k' →
        Γ ≤ Γ' → k' ≤ k → ∀ g,
          A Γ' k' (SchwartzBruhat.ofElem Γ k π hs hπ g) = SchwartzBruhat.ofElem Γ k π hs hπ g) ∧
      (∀ Γ k Γ' k' : Subgroup G, IsStructuralPair Γ k → IsStructuralPair Γ' k' →
        Γ ≤ Γ' → k' ≤ k → ∀ f, A Γ k (A Γ' k' f) = A Γ k f) ∧
      (∀ (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
        (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
        (hπ : IsElemPresentation Γ k π)
        (Γ' k' : Subgroup G) (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
        (π' : ↥Γ' →* Multiplicative (ElemGroup m' n' r' s' d')) (hs' : IsStructuralPair Γ' k')
        (hπ' : IsElemPresentation Γ' k' π'),
        ∃ T : ElemSchwartz m n r s d →ₗ[ℂ] ElemSchwartz m' n' r' s' d', Continuous T ∧
          ∀ g, A Γ' k' (SchwartzBruhat.ofElem Γ k π hs hπ g) =
            SchwartzBruhat.ofElem Γ' k' π' hs' hπ' (T g)) := by
  sorry

end MasulloGRH
