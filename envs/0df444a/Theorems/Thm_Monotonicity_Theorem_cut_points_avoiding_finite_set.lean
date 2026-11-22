-- Prove2me | Theorems.Thm_Monotonicity_Theorem_cut_points_avoiding_finite_set
-- name    : Monotonicity_Theorem.cut_points_avoiding_finite_set
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-12T20:07:14.372515+00:00
-- url     : https://prove2.me/theorems/11b7e62e-65dc-4dd8-8974-7a39cec138e0
-- title:
--   Cut points avoiding a finite set
-- statement:
--   Let $D$ be a dense linear order without endpoints, let $F$ be a finite subset of the line (finiteness in the sense of `IsFinite1`: the first coordinates of the members of $F$ are exactly the entries of some finite list), and let $a < b$.
--
--   **Claim.** There are finitely many cut points
--
--   $$a = p_0 < p_1 < \cdots < p_k = b$$
--
--   such that none of the intervening open intervals $(p_i, p_{i+1})$ meets $F$.
--
--   This is the purely order-theoretic half of the finite-partition step of the Monotonicity Theorem: it converts a finite exceptional set into an explicit finite chain of cut points whose open pieces avoid it. The proof is by induction on the list witnessing the finiteness of $F$: if the first listed value $c$ does not satisfy $a < c < b$, a chain avoiding the remaining values already works, because every open piece is contained in $(a,b)$; if $a < c < b$, one concatenates a chain for the remaining values on $(a,c)$ with a chain for the remaining values on $(c,b)$, and $c$ itself becomes a cut point, so no open piece contains it.
-- source:
--   Lou van den Dries, Tame Topology and O-minimal Structures, LMS Lecture Note Series 248, CUP 1998, Chapter 3, Section 1 (Monotonicity Theorem); order-combinatorial step turning the finite exceptional set into cut points a = p_0 < ... < p_k = b.

import Definitions.Def_Monotonicity_Theorem_Framework

theorem Monotonicity_Theorem.cut_points_avoiding_finite_set {R : Type} (D : DenseLinearOrderNoEndpoints R)
    {F : Set (Power R 1)} (hF : IsFinite1 F) {a b : Power R 1} (hab : Lt1 D a b) :
    exists k : Nat, exists p : Fin (k + 1) -> Power R 1,
      p 0 = a /\ p (Fin.last k) = b /\
      (forall i : Fin k, Lt1 D (p i.castSucc) (p i.succ)) /\
      (forall i : Fin k, forall x : Power R 1,
        openInterval D (Endpoint.finite ((p i.castSucc) 0)) (Endpoint.finite ((p i.succ) 0)) x ->
          Not (F x)) := by sorry
