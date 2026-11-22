-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_of_continuousLinearEquiv_elemSchwartz
-- name    : MasulloGRH.nuclear_of_continuousLinearEquiv_elemSchwartz
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T18:40:52.008771+00:00
-- url     : https://prove2.me/theorems/6d4336a4-6736-423c-9544-e8ce4f905599
-- title:
--   Spaces isomorphic to an elementary Schwartz space are nuclear, in any universe
-- statement:
--   Let $E=\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F_0$ be an elementary abelian Lie group, where $F_0=\prod_i\mathbb Z/d_i$ is finite, and let $\mathcal S(E)$ be its Schwartz space. If a complex topological vector space $V$, in an arbitrary universe, is topologically isomorphic to $\mathcal S(E)$, then $V$ is nuclear:
--   $$V\simeq\mathcal S(E)\ \Longrightarrow\ V\ \text{is nuclear}.$$
--   This lets nuclearity of $\mathcal S(E)$ (Lemma D.1.3.7) pass to Schwartz–Bruhat spaces $\mathcal S(H)$ of groups $H$ in any universe, such as $\mathcal S(G/k)$.
--
--   *Formalization note.* The definition `IsNuclear` quantifies over test spaces in the same universe, so the transfer from `Type 0` is not automatic.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Lemma D.1.3.7(3) and Definition C.2.4.1

import Definitions.Def_MasulloGRH_LocallyConvex
import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

universe u

namespace MasulloGRH

theorem nuclear_of_continuousLinearEquiv_elemSchwartz (F : Type u) [AddCommGroup F] [Module ℂ F]
    [TopologicalSpace F] (m n r s : ℕ) (d : Fin s → ℕ) (hd : ∀ i, d i ≠ 0)
    (e : F ≃L[ℂ] ElemSchwartz m n r s d) : IsNuclear F := by
  sorry

end MasulloGRH
