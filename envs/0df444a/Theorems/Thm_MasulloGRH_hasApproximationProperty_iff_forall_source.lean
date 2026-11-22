-- Prove2me | Theorems.Thm_MasulloGRH_hasApproximationProperty_iff_forall_source
-- name    : MasulloGRH.hasApproximationProperty_iff_forall_source
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:22:35.745825+00:00
-- url     : https://prove2.me/theorems/11506967-896b-47d7-908f-4cca26cbe5e7
-- title:
--   Approximation property $\iff$ finite-rank maps are dense in $\mathscr L_\gamma(F,E)$ for every Hausdorff locally convex $F$
-- statement:
--   **Equivalent form of the approximation property: approximation of maps into $E$.**
--
--   All vector spaces are over $\mathbb C$. A subset $K$ of a topological vector space is **pre-compact** if for every neighbourhood $U$ of $0$ it is covered by finitely many translates of $U$. For topological vector spaces $E$, $F$, let $\mathscr L_\gamma(E,F)$ be the space of continuous linear maps with the topology of uniform convergence on the pre-compact subsets of $E$, and let
--   $$\lambda:E'\otimes F\to\mathscr L(E,F),\qquad\lambda(\varphi\otimes f)=\langle\cdot,\varphi\rangle\,f,$$
--   whose image consists of the continuous linear maps of finite rank $x\mapsto\sum_{i=1}^N\varphi_i(x)f_i$. A space $E$ has the **approximation property** if the identity of $E$ lies in the closure of $\lambda(E'\otimes E)$ in $\mathscr L_\gamma(E,E)$.
--
--   Let $E$ be a Hausdorff locally convex space. The following are equivalent:
--
--   1. $E$ has the approximation property.
--   2. For every Hausdorff locally convex space $F$, the image of $F'\otimes E$ under $\lambda$ is dense in $\mathscr L_\gamma(F,E)$: for every continuous linear map $T:F\to E$, every pre-compact $K\subseteq F$ and every neighbourhood $U$ of $0$ in $E$ there are $\psi_1,\dots,\psi_N\in F'$ and $x_1,\dots,x_N\in E$ with
--   $$Ty-\sum_{i=1}^{N}\psi_i(y)\,x_i\in U\qquad\text{for all }y\in K.$$
--
--   This is the equivalence (1)$\Leftrightarrow$(4) of Lemma C.2.4.15 (again with condition (2) of the lemma as the special case $F=E$).
--
--   **Formalization Note.** `HasApproximationProperty ℂ E` and `IsPrecompact` are the definitions of `Def_TopologicalTensorProduct_ApproximationProperty`; density in $\mathscr L_\gamma(F,E)$ is written out as the displayed approximation statement. The spaces $F$ range over the universe of $E$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 689–690, Lemma C.2.4.15, (1)⇔(2)⇔(4); classical reference: H. H. Schaefer with M. P. Wolff, Topological Vector Spaces, 2nd ed., Springer, Ch. III, 9.1

import Definitions.Def_MasulloGRH_LocallyConvex
import Definitions.Def_TopologicalTensorProduct_ApproximationProperty

open Topology Filter TopologicalTensorProduct
set_option autoImplicit false
universe u

namespace MasulloGRH

theorem hasApproximationProperty_iff_forall_source (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsHLCS E) :
    HasApproximationProperty ℂ E ↔
      ∀ (F : Type u) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F], IsHLCS F →
        ∀ (T : F →L[ℂ] E) (K : Set F), IsPrecompact K → ∀ U ∈ 𝓝 (0 : E),
          ∃ (N : ℕ) (ψ : Fin N → StrongDual ℂ F) (x : Fin N → E),
            ∀ y ∈ K, T y - ∑ i, ψ i y • x i ∈ U := by sorry

end MasulloGRH
