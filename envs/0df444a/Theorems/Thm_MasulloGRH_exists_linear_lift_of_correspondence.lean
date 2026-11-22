-- Prove2me | Theorems.Thm_MasulloGRH_exists_linear_lift_of_correspondence
-- name    : MasulloGRH.exists_linear_lift_of_correspondence
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T17:23:08.277916+00:00
-- url     : https://prove2.me/theorems/9c58154a-b10c-4f3b-a4f2-4de77ac35f71
-- title:
--   A correspondence between elementary groups lifts linearly on identity components
-- statement:
--   Let $P$ be a locally compact abelian group, $P_0\le P$ an open subgroup, and let
--   $$\alpha:P_0\to E=\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F,\qquad \beta:P\to E'=\mathbb R^{m'}\times\mathbb T^{n'}\times\mathbb Z^{r'}\times F'$$
--   be continuous open homomorphisms, with $\ker\alpha$ compact. Write $\mathcal L(x,t)=(x,[t],0,0)$ for the covering map of the identity component $\mathbb R^m\times\mathbb T^n$ of $E$, and similarly $\mathcal L'$ for $E'$. Then there is a real linear map $\Lambda:\mathbb R^{m'}\times\mathbb R^{n'}\to\mathbb R^m\times\mathbb R^n$ such that for every $y'$ some $p\in P_0$ satisfies
--   $$\alpha(p)=\mathcal L(\Lambda y'),\qquad \beta(p)=\mathcal L'(y').$$
--   In other words, the correspondence $\beta\circ\alpha^{-1}$ between the identity components lifts to a linear map of the universal covers.
--
--   Proof: the lifted graph $V=\{(y,y'):\exists p,\ \alpha p=\mathcal L y,\ \beta p=\mathcal L'y'\}$ is an additive subgroup. It is closed because $\alpha$ is proper. Its projection to $\mathbb R^{m'+n'}$ is onto, since $\beta(\alpha^{-1}(\text{identity component}))$ is an open subgroup of $E'$ and so contains its identity component. Write $V=V_{\mathrm{lin}}+D$ with $V_{\mathrm{lin}}$ a subspace and $D$ countable. A Haar-measure (Baire-type) argument shows $V_{\mathrm{lin}}$ already projects onto, and a linear section gives $\Lambda$. This is the key step in transporting Schwartz–Bruhat functions along correspondences (Lemma D.1.5.4).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.1.3 and Lemma D.1.5.4

import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

namespace MasulloGRH

theorem exists_linear_lift_of_correspondence
    (P : Type*) [CommGroup P] [TopologicalSpace P] [IsTopologicalGroup P] [T2Space P]
    [LocallyCompactSpace P] (P₀ : Subgroup P) (hP₀ : IsOpen (P₀ : Set P))
    (m n r s : ℕ) (d : Fin s → ℕ)
    (α : ↥P₀ →* Multiplicative (ElemGroup m n r s d)) (hαc : Continuous α) (hαo : IsOpenMap α)
    (hαk : IsCompact {x : ↥P₀ | α x = 1})
    (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
    (β : P →* Multiplicative (ElemGroup m' n' r' s' d')) (hβc : Continuous β)
    (hβo : IsOpenMap β) :
    ∃ Λ : ((Fin m' → ℝ) × (Fin n' → ℝ)) →ₗ[ℝ] ((Fin m → ℝ) × (Fin n → ℝ)),
      ∀ y' : (Fin m' → ℝ) × (Fin n' → ℝ), ∃ p : P₀,
        α p = Multiplicative.ofAdd ((Λ y').1, fun j => (((Λ y').2 j : ℝ) : UnitAddCircle), 0, 0) ∧
        β p = Multiplicative.ofAdd (y'.1, fun j => ((y'.2 j : ℝ) : UnitAddCircle), 0, 0) := by
  sorry

end MasulloGRH
