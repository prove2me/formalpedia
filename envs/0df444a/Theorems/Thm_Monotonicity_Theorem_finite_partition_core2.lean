-- Prove2me | Theorems.Thm_Monotonicity_Theorem_finite_partition_core2
-- name    : Monotonicity_Theorem.finite_partition_core2
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-14T21:33:54.110054+00:00
-- url     : https://prove2.me/theorems/492497eb-44e6-4048-b880-fcaf97e5a37d
-- title:
--   Finite good partition
-- statement:
--   The partition assembly behind the monotonicity theorem: from the constant, increasing, and decreasing window classes with finite bad locus, cut points giving the same piecewise conclusion, under an explicit domain-inclusion hypothesis.
-- source:
--   van den Dries, Tame Topology and O-Minimal Structures, Ch. 3

import Definitions.Def_Monotonicity_Theorem_Framework2

theorem Monotonicity_Theorem.finite_partition_core2 {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    {a b : Power R 1} (hab : Lt1 a b)
    (hsubIJ : (openInterval (Endpoint.finite (Power.coord1 a)) (Endpoint.finite (Power.coord1 b))).Subset I) :
    ∃ k : Nat, ∃ p : Fin (k + 1) → Power R 1,
      p 0 = a ∧ p (Fin.last k) = b ∧
      (∀ i : Fin k, Lt1 (p i.castSucc) (p i.succ)) ∧
      (∀ i : Fin k,
        let J : Set (Power R 1) := openInterval (Endpoint.finite ((p i.castSucc) 0)) (Endpoint.finite ((p i.succ) 0))
        (((∀ x (hxI : I x), J x → ∀ y (hyI : I y), J y ->
          f.toFun (Subtype.mk x hxI) = f.toFun (Subtype.mk y hyI)) ∧
          J.Subset (ContinuousPoints I (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun))) ∨
         (((∀ x (hxI : I x), J x → ∀ y (hyI : I y), J y → Lt1 x y ->
            Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1) ∨
           (∀ x (hxI : I x), J x → ∀ y (hyI : I y), J y → Lt1 x y ->
            Lt1 (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1)) ∧
          J.Subset (ContinuousPoints I (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun))))) := by sorry
