-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhat_equiv_elem_of_minimal_goodSubgroup
-- name    : MasulloGRH.schwartzBruhat_equiv_elem_of_minimal_goodSubgroup
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T18:16:53.175073+00:00
-- url     : https://prove2.me/theorems/fe59ccc3-2204-4bff-a1d0-74d21ebc692c
-- title:
--   If $H$ has a smallest good subgroup, $\mathcal S(H)$ is an elementary Schwartz space
-- statement:
--   Let $H$ be a Hausdorff locally compact abelian group. Let $k_0\le H$ be a good subgroup such that $(H,k_0)$ is a structural pair, with a presentation $\pi_0\colon H/k_0\simeq E_0=\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$. Assume $k_0$ is the **smallest** good subgroup: $k_0\subseteq k$ for every good subgroup $k\le H$.
--
--   Then the inclusion $\mathcal S(E_0)\to\mathcal S(H)$, $g\mapsto g\circ\pi_0$, is a linear topological isomorphism. In particular $\mathcal S(H)$ is a Fréchet space.
--
--   For an elementary abelian Lie group $H$ (e.g. $H=G/k$ for a good subgroup $k$ of a second countable $\mathbb R_{>0}$-modulated group $G$), the trivial subgroup is the smallest good subgroup. So $\mathcal S(H)\simeq\mathcal S(\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F)$ is nuclear Fréchet (Lemma D.1.3.7(3)). These are the target spaces of the weight maps $T_a$ defining the stages $\mathcal S_I(k,G)$ in Definition D.3.3.3.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Definitions D.1.5.1–D.1.5.4, Lemma D.1.3.7(3), Definition D.3.3.3

import Definitions.Def_MasulloGRH_LocallyConvex
import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

universe u

namespace MasulloGRH

theorem schwartzBruhat_equiv_elem_of_minimal_goodSubgroup (H : Type u) [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [LocallyCompactSpace H]
    (k₀ : Subgroup H) (m n r s : ℕ) (d : Fin s → ℕ)
    (π₀ : (⊤ : Subgroup H) →* Multiplicative (ElemGroup m n r s d))
    (hs₀ : IsStructuralPair ⊤ k₀) (hπ₀ : IsElemPresentation ⊤ k₀ π₀)
    (hmin : ∀ k : Subgroup H, IsGoodSubgroup k → k₀ ≤ k) :
    Nonempty (ElemSchwartz m n r s d ≃L[ℂ] SchwartzBruhat H) ∧ IsFrechet (SchwartzBruhat H) := by
  sorry

end MasulloGRH
