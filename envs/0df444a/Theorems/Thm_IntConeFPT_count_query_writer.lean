-- Prove2me | Theorems.Thm_IntConeFPT_count_query_writer
-- name    : IntConeFPT.count_query_writer
-- status  : Open
-- author  : @ohnesorgefelix
-- created : 2026-11-25T11:52:04.864484+00:00
-- url     : https://prove2.me/theorems/63bfb116-9f20-40ab-b094-a74e7d72ba8c
-- title:
--   Output-sensitive construction of the two counted queries
-- statement:
--   Given the encoded instance $I$ and box bound $M$, form the two counted-solver inputs with cutoff $N_\star$, one for $I$ and one for the homogenized instance. Return a framed triple containing $I$ and the two inputs, in time polynomial in the lengths of $I,M,N_\star$. This is solely the query-construction routine: its time budget includes the length of the binary cutoff it actually writes.
-- source:
--   Jansen, Ohnesorge and Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, https://arxiv.org/abs/2609.31328, §3.6, proof of Theorem 1, p.18, and formula (3.4).

import Definitions.Def_IntConeFPT_Homogenized
import Definitions.Def_IntConeFPT_Machine
open OnlineCRS.Combine IntConeFPT

theorem IntConeFPT.count_query_writer :
    let frame := fun (x y : List Sym) => x.flatMap (fun s => [(0 : Sym),s]) ++ 1::y
    ∃ d : ℕ, ∃ P : Machine, ∀ I : Instance, I.Valid → ∀ M : ℕ, 1 ≤ M →
      let n := Nstar I.τ I.d I.k (coeffBoundU I M)
      let q := encInstance I ++ encNat n ++ [3]
      let h := encInstance (homInstance I) ++ encNat n ++ [3]
      RunsWithin P (frame (encInstance I) (encNat M)) (frame (frame (encInstance I) h) q)
        (((encInstance I).length + (encNat M).length + (encNat n).length + 2 : ℝ)^d) := by sorry
