-- Prove2me | Theorems.Thm_MasulloGRH_hasApproximationProperty_iff_forall_target
-- name    : MasulloGRH.hasApproximationProperty_iff_forall_target
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:22:33.723245+00:00
-- url     : https://prove2.me/theorems/869a8c27-7cf1-4bc7-98b7-b59f71ee11d1
-- title:
--   Approximation property $\iff$ finite-rank maps are dense in $\mathscr L_\gamma(E,F)$ for every Hausdorff locally convex $F$
-- statement:
--   **Equivalent form of the approximation property: approximation of maps out of $E$.**
--
--   All vector spaces are over $\mathbb C$. A subset $K$ of a topological vector space is **pre-compact** if for every neighbourhood $U$ of $0$ it is covered by finitely many translates of $U$. For topological vector spaces $E$, $F$, let $\mathscr L_\gamma(E,F)$ be the space of continuous linear maps with the topology of uniform convergence on the pre-compact subsets of $E$, and let
--   $$\lambda:E'\otimes F\to\mathscr L(E,F),\qquad\lambda(\varphi\otimes f)=\langle\cdot,\varphi\rangle\,f,$$
--   whose image consists of the continuous linear maps of finite rank $x\mapsto\sum_{i=1}^N\varphi_i(x)f_i$. A space $E$ has the **approximation property** if the identity of $E$ lies in the closure of $\lambda(E'\otimes E)$ in $\mathscr L_\gamma(E,E)$.
--
--   Let $E$ be a Hausdorff locally convex space. The following are equivalent:
--
--   1. $E$ has the approximation property.
--   2. For every Hausdorff locally convex space $F$, the image of $E'\otimes F$ under $\lambda$ is dense in $\mathscr L_\gamma(E,F)$: for every continuous linear map $T:E\to F$, every pre-compact $K\subseteq E$ and every neighbourhood $V$ of $0$ in $F$ there are $\varphi_1,\dots,\varphi_N\in E'$ and $y_1,\dots,y_N\in F$ with
--   $$Tx-\sum_{i=1}^{N}\varphi_i(x)\,y_i\in V\qquad\text{for all }x\in K.$$
--
--   This is the equivalence (1)$\Leftrightarrow$(3) of Lemma C.2.4.15; taking $F=E$ in 2 gives condition (2) of the lemma (density of the finite-rank maps in $\mathscr L_\gamma(E,E)$), which therefore is also equivalent. The approximation property is the hypothesis under which traces of nuclear operators are well behaved in §C.3 of the paper.
--
--   **Formalization Note.** `HasApproximationProperty ℂ E` and `IsPrecompact` are the definitions of `Def_TopologicalTensorProduct_ApproximationProperty`; density in $\mathscr L_\gamma(E,F)$ is written out as the displayed approximation statement (basic neighbourhoods of $T$ are $\{S:(S-T)(K)\subseteq V\}$), so no topology on a space of operators is involved. The spaces $F$ range over the universe of $E$ (so that $F=E$ is allowed).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 689–690, Lemma C.2.4.15, (1)⇔(2)⇔(3); classical reference: H. H. Schaefer with M. P. Wolff, Topological Vector Spaces, 2nd ed., Springer, Ch. III, 9.1

import Definitions.Def_MasulloGRH_LocallyConvex
import Definitions.Def_TopologicalTensorProduct_ApproximationProperty

open Topology Filter TopologicalTensorProduct
set_option autoImplicit false
universe u

namespace MasulloGRH

theorem hasApproximationProperty_iff_forall_target (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsHLCS E) :
    HasApproximationProperty ℂ E ↔
      ∀ (F : Type u) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F], IsHLCS F →
        ∀ (T : E →L[ℂ] F) (K : Set E), IsPrecompact K → ∀ V ∈ 𝓝 (0 : F),
          ∃ (N : ℕ) (φ : Fin N → StrongDual ℂ E) (y : Fin N → F),
            ∀ x ∈ K, T x - ∑ i, φ i x • y i ∈ V := by sorry

end MasulloGRH
