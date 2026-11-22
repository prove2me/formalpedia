-- Prove2me | Theorems.Thm_MasulloGRH_exists_cofinal_fg_subgroups_of_countable
-- name    : MasulloGRH.exists_cofinal_fg_subgroups_of_countable
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T18:08:23.041626+00:00
-- url     : https://prove2.me/theorems/0f698055-2948-45ec-8e0f-43412620bf50
-- title:
--   A countable abelian group has a cofinal increasing sequence of finitely generated subgroups
-- statement:
--   Let $A$ be a countable abelian group. Then there is an increasing sequence
--   $$A_0\subseteq A_1\subseteq A_2\subseteq\cdots$$
--   of finitely generated subgroups of $A$ that is cofinal among finitely generated subgroups: every finitely generated subgroup $H\le A$ is contained in some $A_N$.
--
--   In Masullo's §D.3.3 this is applied to the discrete countable dual $\widehat{G^1}$ of the compact kernel $G^1$ of the module of a second countable $\mathbb R_{>0}$-modulated group. The good subgroups $k\subseteq G^1$ are those whose orthogonal in $\widehat{G^1}$ is finitely generated. So the orthogonals $k_N=A_N^{\perp}$ form a decreasing sequence of good subgroups such that every good subgroup contains some $k_N$ (Remark D.3.3.8). This gives the countable stages of $\mathcal S_I(G)$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.3.3 (p. 804) and Remark D.3.3.8 (p. 807)

import Mathlib

set_option autoImplicit false

namespace MasulloGRH

theorem exists_cofinal_fg_subgroups_of_countable (A : Type*) [CommGroup A] [Countable A] :
    ∃ S : ℕ → Subgroup A, Monotone S ∧ (∀ N, (S N).FG) ∧
      ∀ H : Subgroup A, H.FG → ∃ N, H ≤ S N := by
  sorry

end MasulloGRH
