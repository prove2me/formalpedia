-- Prove2me | Theorems.Thm_Monotonicity_Theorem_monotonicity_theorem2
-- name    : Monotonicity_Theorem.monotonicity_theorem2
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-14T23:07:20.360339+00:00
-- url     : https://prove2.me/theorems/c72c2d07-1831-41d4-9e8e-6f82a50ba689
-- title:
--   Monotonicity theorem
-- statement:
--   Let an o-minimal structure M be given on a dense linear order without endpoints. For a definable function f on an infinite definable interval I, and ordered endpoints a and b, there are finitely many cut points from a to b. On each intervening open interval, f is constant, or strictly increasing and continuous, or strictly decreasing and continuous, with continuity expressed by ContinuousPoints.
-- source:
--   van den Dries, Tame Topology and O-Minimal Structures, Ch. 3

import Definitions.Def_Monotonicity_Theorem_Framework2

theorem Monotonicity_Theorem.monotonicity_theorem2
    {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R)
    {a b : Power R 1} (hab : Lt1 a b)
    (f : DefinableFunction M
      (openInterval (Endpoint.finite (Power.coord1 a))
        (Endpoint.finite (Power.coord1 b)))
      (Set.univ : Set (Power R 1))) :
    exists (k : Nat), exists (p : Fin (k + 1) -> Power R 1),
      p 0 = a /\
      p (Fin.last k) = b /\
      (forall (i : Fin k), Lt1 (p i.castSucc) (p i.succ)) /\
      (forall (i : Fin k),
        let J : Set (Power R 1) :=
          openInterval
            (Endpoint.finite ((p i.castSucc) 0))
            (Endpoint.finite ((p i.succ) 0))
        (forall (x : {x : Power R 1 //
            (openInterval (Endpoint.finite (Power.coord1 a))
              (Endpoint.finite (Power.coord1 b))) x}),
          forall (y : {y : Power R 1 //
            (openInterval (Endpoint.finite (Power.coord1 a))
              (Endpoint.finite (Power.coord1 b))) y}),
          J x.1 -> J y.1 ->
          f.toFun x = f.toFun y)
        \/
        ((forall (x : {x : Power R 1 //
            (openInterval (Endpoint.finite (Power.coord1 a))
              (Endpoint.finite (Power.coord1 b))) x}),
            forall (y : {y : Power R 1 //
            (openInterval (Endpoint.finite (Power.coord1 a))
              (Endpoint.finite (Power.coord1 b))) y}),
            J x.1 -> J y.1 -> Lt1 x.1 y.1 ->
            Lt1 (f.toFun x).1 (f.toFun y).1)
          \/
          (forall (x : {x : Power R 1 //
            (openInterval (Endpoint.finite (Power.coord1 a))
              (Endpoint.finite (Power.coord1 b))) x}),
            forall (y : {y : Power R 1 //
            (openInterval (Endpoint.finite (Power.coord1 a))
              (Endpoint.finite (Power.coord1 b))) y}),
            J x.1 -> J y.1 -> Lt1 x.1 y.1 ->
            Lt1 (f.toFun y).1 (f.toFun x).1))
        /\ J.Subset
            (ContinuousPoints
              (openInterval (Endpoint.finite (Power.coord1 a))
                (Endpoint.finite (Power.coord1 b)))
              (FunctionGraph (R := R) (m := 1) (n := 1)
                (A := openInterval (Endpoint.finite (Power.coord1 a))
                  (Endpoint.finite (Power.coord1 b)))
                (B := Set.univ)
                f.toFun))) := by sorry
