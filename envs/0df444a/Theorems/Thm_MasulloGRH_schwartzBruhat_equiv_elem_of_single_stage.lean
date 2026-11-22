-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhat_equiv_elem_of_single_stage
-- name    : MasulloGRH.schwartzBruhat_equiv_elem_of_single_stage
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T18:14:56.879684+00:00
-- url     : https://prove2.me/theorems/f7e4f60f-83c9-4b5d-b654-ece573e7bc0d
-- title:
--   A Schwartz–Bruhat space with a single dominating stage is an elementary Schwartz space
-- statement:
--   Let $H$ be an abelian topological group and $(\Gamma_0,k_0)$ a structural pair in $H$, with a presentation $\pi_0\colon\Gamma_0/k_0\simeq E_0=\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$. Assume this stage dominates all others: for every structural pair $(\Gamma,k)$ with presentation $\pi\colon\Gamma/k\simeq E$, there is a continuous linear map $\varphi\colon\mathcal S(E)\to\mathcal S(E_0)$ with
--   $$\iota_{\Gamma,k,\pi}=\iota_{\Gamma_0,k_0,\pi_0}\circ\varphi,$$
--   where $\iota$ denotes the inclusion $\mathcal S(\Gamma/k)\to\mathcal S(H)$ (pull back, then extend by zero).
--
--   Then $\iota_{\Gamma_0,k_0,\pi_0}\colon\mathcal S(E_0)\to\mathcal S(H)$ is a linear topological isomorphism. In particular $\mathcal S(H)$ is a Fréchet space.
--
--   The draft uses this for the quotients $H=G/k$ by good subgroups $k$, which are elementary abelian Lie groups. There $\mathcal S(G/k)$ is identified with the nuclear Fréchet space of smooth rapidly decreasing functions on $G/k$ (Lemma D.1.3.7(3)). This is needed for the stages $\mathcal S_I(k,G)$ of Definition D.3.3.3.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Definition D.1.5.3, D.1.5.4, Lemma D.1.3.7(3) and Example D.3.3.5

import Definitions.Def_MasulloGRH_LocallyConvex
import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

universe u

namespace MasulloGRH

theorem schwartzBruhat_equiv_elem_of_single_stage (H : Type u) [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    (Γ₀ k₀ : Subgroup H) (m n r s : ℕ) (d : Fin s → ℕ)
    (π₀ : Γ₀ →* Multiplicative (ElemGroup m n r s d)) (hs₀ : IsStructuralPair Γ₀ k₀)
    (hπ₀ : IsElemPresentation Γ₀ k₀ π₀)
    (hfac : ∀ (Γ k : Subgroup H) (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
      (π : Γ →* Multiplicative (ElemGroup m' n' r' s' d')) (hs : IsStructuralPair Γ k)
      (hπ : IsElemPresentation Γ k π),
      ∃ φ : ElemSchwartz m' n' r' s' d' →ₗ[ℂ] ElemSchwartz m n r s d, Continuous φ ∧
        ∀ g, SchwartzBruhat.ofElem Γ k π hs hπ g = SchwartzBruhat.ofElem Γ₀ k₀ π₀ hs₀ hπ₀ (φ g)) :
    Nonempty (ElemSchwartz m n r s d ≃L[ℂ] SchwartzBruhat H) ∧ IsFrechet (SchwartzBruhat H) := by
  sorry

end MasulloGRH
