-- Prove2me | Theorems.Thm_MasulloGRH_isCompactOperator_of_isNuclearMap
-- name    : MasulloGRH.isCompactOperator_of_isNuclearMap
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:24:47.695227+00:00
-- url     : https://prove2.me/theorems/6a3eae31-e268-4e8e-ba40-eb77c016acc1
-- title:
--   Nuclear maps between Hausdorff locally convex spaces are compact
-- statement:
--   **Nuclear maps are compact.**
--
--   All vector spaces are over $\mathbb C$. A **Banach disc** of a topological vector space $F$ is a non-empty bounded convex circled subset $B\subseteq F$ whose linear span $F_B=\bigcup_{m\ge1}mB$, normed by the Minkowski functional $p_B$ of $B$, is a Banach space. A continuous linear map $T:E\to F$ is **nuclear** if it has a **nuclear representation**
--   $$T=\sum_{n}\lambda_n\,\langle\cdot,\varphi_n\rangle\,y_n ,$$
--   that is, $Tx=\sum_n\lambda_n\varphi_n(x)\,y_n$ for all $x\in E$, where $\sum_n|\lambda_n|<\infty$, $(\varphi_n)$ is an equicontinuous sequence in the dual $E'$ and $(y_n)$ is a sequence contained in a Banach disc of $F$.
--
--   Let $E$ and $F$ be Hausdorff locally convex spaces and let $T:E\to F$ be a nuclear map. Then $T$ is **compact**: there is a neighbourhood $U$ of $0$ in $E$ whose image $T(U)$ is contained in a compact subset of $F$; equivalently,
--   $$\overline{T(U)}\subseteq F\ \text{ is compact for some $0$-neighbourhood }U\subseteq E .$$
--
--   This is the basic link between nuclearity and compactness (the paper deduces it from the series representation of Lemma C.3.1.2 and uses it, e.g., to see that nuclear operators on a Hilbert space are compact, so that their singular values are defined).
--
--   **Formalization Note.** `IsHLCS` (from `Def_MasulloGRH_LocallyConvex`) means that the topology is defined by a family of seminorms and is Hausdorff. `IsNuclearMap`, `IsNuclearRepr` and `IsBanachDisc` are the definitions of `Def_MasulloGRH_NuclearMap`: a nuclear representation consists of sequences indexed by $\mathbb N$, the series converges unconditionally in $F$ (`HasSum`), and the Minkowski functional $p_B$ is Mathlib's `gauge B`. Compactness is Mathlib's `IsCompactOperator T`: there is a compact $K\subseteq F$ with $T^{-1}(K)$ a neighbourhood of $0$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 694, §C.3.1 (paragraph after Lemma C.3.1.2), and p. 702 (proof of Proposition C.3.5.1, where the fact is cited); classical reference: H. H. Schaefer with M. P. Wolff, Topological Vector Spaces, 2nd ed., Springer, Ch. III, Cor. 1 to 7.1

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex
import Definitions.Def_MasulloGRH_NuclearMap

open Filter Topology
set_option autoImplicit false

namespace MasulloGRH

theorem isCompactOperator_of_isNuclearMap {E F : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (hE : IsHLCS E) (hF : IsHLCS F) (T : E →L[ℂ] F) (hT : IsNuclearMap T) :
    IsCompactOperator T := by sorry

end MasulloGRH
