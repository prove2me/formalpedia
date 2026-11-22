-- Prove2me | Theorems.Thm_MasulloGRH_correspondence_growth_bound
-- name    : MasulloGRH.correspondence_growth_bound
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T17:33:38.662816+00:00
-- url     : https://prove2.me/theorems/a526b86d-4dae-4119-a51a-6f7ce86ba75c
-- title:
--   Linear growth bound for a correspondence between elementary groups
-- statement:
--   Let $P$ be a locally compact abelian group and $P_0\le P$ an open subgroup. Let
--   $$\alpha:P_0\to E=\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F\quad(F \text{ finite})$$
--   be a continuous open homomorphism with compact kernel, and let $\beta:P\to E'=\mathbb R^{m'}\times\mathbb T^{n'}\times\mathbb Z^{r'}\times F'$ be continuous. Measure size by $N(x,z,a,b)=\|x\|+\|a\|$, ignoring the compact factors. Then $\beta$ grows at most linearly relative to $\alpha$: there are constants $A,B$ with
--   $$N'(\beta(p))\le A\,N(\alpha(p))+B\qquad(p\in P_0).$$
--   Proof: $\alpha$ is proper, so $N'\circ\beta$ is bounded on each set $\{N(\alpha p)\le R\}$. Write $\alpha(p)=(x,0,0,0)+(0,z,0,0)+(0,0,a,b)$. The real part is handled by divisibility, taking a $\lceil\|x\|\rceil$-th power of a preimage of $(x/\lceil\|x\|\rceil,0,0,0)$. The torus part is bounded. The discrete part is handled by bounded rounding in the subgroup of $\mathbb Z^r$ it ranges over (subgroups of $\mathbb Z^r$ are undistorted). This growth bound is what makes the transport of rapid-decay functions along the correspondence $\beta\circ\alpha^{-1}$ preserve the Schwartz–Bruhat seminorms (Lemma D.1.5.4).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Lemma D.1.5.4

import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

namespace MasulloGRH

theorem correspondence_growth_bound
    (P : Type*) [CommGroup P] [TopologicalSpace P] [IsTopologicalGroup P] [T2Space P]
    [LocallyCompactSpace P] (P₀ : Subgroup P) (hP₀ : IsOpen (P₀ : Set P))
    (m n r s : ℕ) (d : Fin s → ℕ) (hd : ∀ i, d i ≠ 0)
    (α : ↥P₀ →* Multiplicative (ElemGroup m n r s d)) (hαc : Continuous α) (hαo : IsOpenMap α)
    (hαk : IsCompact {x : ↥P₀ | α x = 1})
    (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
    (β : P →* Multiplicative (ElemGroup m' n' r' s' d')) (hβc : Continuous β) :
    ∃ A B : ℝ, ∀ p : P₀,
      ‖(Multiplicative.toAdd (β p)).1‖ + ‖(Multiplicative.toAdd (β p)).2.2.1‖ ≤
        A * (‖(Multiplicative.toAdd (α p)).1‖ + ‖(Multiplicative.toAdd (α p)).2.2.1‖) + B := by
  sorry

end MasulloGRH
