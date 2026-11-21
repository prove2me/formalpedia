-- Prove2me | Theorems.Thm_MasulloGRH_bounded_lifting_of_stage_factorizations
-- name    : MasulloGRH.bounded_lifting_of_stage_factorizations
-- status  : Proved
-- author  : @ghseeli
-- created : 2026-11-20T22:38:40.070464+00:00
-- url     : https://prove2.me/theorems/ec23352c-a857-4bde-9507-b0ff3de27655
-- title:
--   Bounded-set lifting through factorizations of strict inductive-limit stages
-- statement:
--   Let $E$ and $Q$ be complex vector spaces equipped with topologies, with $Q$ a Hausdorff locally convex topological vector space. Suppose $Q$ is the strict locally convex inductive limit of an increasing exhaustive sequence of closed subspaces $Y_n$, each carrying its subspace topology.
--
--   For each $n$, let $F_n,P_n$ be complex vector spaces with topologies. Suppose there are continuous linear maps $j_n:F_n\to E$ and $v_n:Y_n\to P_n$, maps $p_n:F_n\to P_n$ and $r_n:P_n\to Q$, and a map $q:E\to Q$, such that
--   $$
--   q\circ j_n=r_n\circ p_n,\qquad r_n\circ v_n=\iota_n,
--   $$
--   where $\iota_n:Y_n\hookrightarrow Q$ is the inclusion. If each $p_n$ lifts bounded sets, then so does $q$:
--   $$
--   \forall B\subset Q\text{ bounded},\quad
--   \exists D\subset E\text{ bounded},\quad B\subset q(D).
--   $$
--   This abstracts the bounded-set assembly in the last paragraph of the proof of Corollary C.1.5.13. There the auxiliary quotient $P_n$ is a suitable quotient of a nuclear Frechet step, and $v_n$ comes from the factorization argument. This lemma does not assert existence of those factorizations or prove the bounded lifting property of the auxiliary quotients.
--
--   **Formalization Note** Only $j_n$ and $v_n$ need to be continuous and linear for this assembly step; $p_n,r_n,q$ may be arbitrary functions satisfying the displayed conditions. The Lean statement accordingly assumes only vector-space topologies on $E,F_n,P_n$, and explicitly assumes a Hausdorff locally convex topology on $Q$. The topology of $Q$ is specified as the finest locally convex topology making all stage inclusions continuous. Bounded means von Neumann bounded.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, Corollary C.1.5.13, proof, p. 669, final paragraph; bounded-set concentration is Proposition C.1.5.3, pp. 664–665. This is an abstraction of the final assembly step, not the entire corollary. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloGRH_LocallyConvex
set_option autoImplicit false
open Set MasulloGRH

theorem MasulloGRH.bounded_lifting_of_stage_factorizations
    (E Q : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q]
    (hQ : IsHLCS Q) (Y : ℕ → Submodule ℂ Q) (hmono : Monotone Y)
    (hexh : ∀ y : Q, ∃ n, y ∈ Y n) (hcl : ∀ n, IsClosed (Y n : Set Q))
    (htop : ‹TopologicalSpace Q› =
      sInf {t | IsLocallyConvexTopology Q t ∧ ∀ n, @Continuous (Y n) Q _ t Subtype.val})
    (F P : ℕ → Type*) [∀ n, AddCommGroup (F n)] [∀ n, Module ℂ (F n)]
    [∀ n, TopologicalSpace (F n)] [∀ n, AddCommGroup (P n)] [∀ n, Module ℂ (P n)]
    [∀ n, TopologicalSpace (P n)]
    (q : E → Q) (j : ∀ n, F n →L[ℂ] E) (p : ∀ n, F n → P n)
    (r : ∀ n, P n → Q) (v : ∀ n, Y n →L[ℂ] P n)
    (hlift : ∀ n, LiftsBoundedSets (p n))
    (hcomm : ∀ n x, q (j n x) = r n (p n x))
    (hfactor : ∀ n y, r n (v n y) = (y : Q)) :
    LiftsBoundedSets q := by sorry
