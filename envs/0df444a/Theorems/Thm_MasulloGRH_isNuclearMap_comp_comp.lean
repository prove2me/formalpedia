-- Prove2me | Theorems.Thm_MasulloGRH_isNuclearMap_comp_comp
-- name    : MasulloGRH.isNuclearMap_comp_comp
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:24:44.147873+00:00
-- url     : https://prove2.me/theorems/d9e53ffe-aae8-47c5-94bf-5859e7454390
-- title:
--   Ideal property of nuclear maps: $S\circ T\circ R$ is nuclear when $T$ is nuclear and $R$, $S$ are continuous linear
-- statement:
--   **Ideal property of nuclear maps.**
--
--   All vector spaces are over $\mathbb C$. A **Banach disc** of a topological vector space $F$ is a non-empty bounded convex circled subset $B\subseteq F$ whose linear span $F_B=\bigcup_{m\ge1}mB$, normed by the Minkowski functional $p_B$ of $B$, is a Banach space. A continuous linear map $T:E\to F$ is **nuclear** if it has a **nuclear representation**
--   $$T=\sum_{n}\lambda_n\,\langle\cdot,\varphi_n\rangle\,y_n ,$$
--   that is, $Tx=\sum_n\lambda_n\varphi_n(x)\,y_n$ for all $x\in E$, where $\sum_n|\lambda_n|<\infty$, $(\varphi_n)$ is an equicontinuous sequence in the dual $E'$ and $(y_n)$ is a sequence contained in a Banach disc of $F$.
--
--   Let $W,E,F,G$ be Hausdorff locally convex spaces, let $T:E\to F$ be a nuclear map and let $R:W\to E$ and $S:F\to G$ be continuous linear maps. Then the composition
--   $$S\circ T\circ R\;:\;W\longrightarrow G$$
--   is nuclear. In particular (taking $R$ or $S$ to be an identity map) $T\circ R$ and $S\circ T$ are nuclear.
--
--   This is the two-sided ideal property of the class of nuclear maps. The paper invokes it in the proof of Lemma C.3.2.2 to see that $A=T\circ A_0$ and $A_1=A_0\circ T$ inherit nuclearity from $A_0$; the nuclearity of $T^{-1}AT$ asserted in Proposition C.3.2.1 is the special case $R=T$, $S=T^{-1}$.
--
--   **Formalization Note.** `IsHLCS` (from `Def_MasulloGRH_LocallyConvex`) means that the topology is defined by a family of seminorms and is Hausdorff. `IsNuclearMap`, `IsNuclearRepr` and `IsBanachDisc` are the definitions of `Def_MasulloGRH_NuclearMap`: a nuclear representation consists of sequences indexed by $\mathbb N$, the series converges unconditionally in $F$ (`HasSum`), and the Minkowski functional $p_B$ is Mathlib's `gauge B`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 696 (proof of Lemma C.3.2.2, where the ideal property is cited) and p. 694 (Proposition C.3.2.1, nuclearity of $T^{-1}AT$); classical reference: H. H. Schaefer with M. P. Wolff, Topological Vector Spaces, 2nd ed., Springer, Ch. III, Cor. 2 to 7.1

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex
import Definitions.Def_MasulloGRH_NuclearMap

open Filter Topology
set_option autoImplicit false

namespace MasulloGRH

theorem isNuclearMap_comp_comp {W E F G : Type*}
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    (hW : IsHLCS W) (hE : IsHLCS E) (hF : IsHLCS F) (hG : IsHLCS G)
    (T : E →L[ℂ] F) (hT : IsNuclearMap T) (R : W →L[ℂ] E) (S : F →L[ℂ] G) :
    IsNuclearMap (S ∘L T ∘L R) := by sorry

end MasulloGRH
