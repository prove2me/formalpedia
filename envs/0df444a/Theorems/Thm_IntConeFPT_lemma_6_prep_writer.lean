-- Prove2me | Theorems.Thm_IntConeFPT_lemma_6_prep_writer
-- name    : IntConeFPT.lemma_6_prep_writer
-- status  : Open
-- author  : @ohnesorgefelix
-- created : 2026-11-26T09:12:30.367869+00:00
-- url     : https://prove2.me/theorems/bffddda8-8837-5000-b561-b4a745a36750
-- title:
--   Lemma 6 fractional-oracle query preparation and context framing
-- statement:
--   There exist an absolute constant $C \in \mathbb{N}$ and a deterministic TM2 machine $P$ over $\{0,1,2,3\}$ that, given a valid instance $I$, block type $t$, residue vector $r$, integral vector $z \in \mathbb{Z}^d$, rational vector $w \in \mathbb{Q}^k$, and integer multiplicity $n \ge 1$, transforms the encoded Lemma 6 input `(encLocal I t r ++ encIntVec z ++ encVec w ++ encNat n ++ [3])` into the framed pair `frame ctx inp5` within polynomial time $(|\text{inp}| + 2)^C$, where `ctx` preserves $(d, k, r, z, n)$ and `inp5` formats the Lemma 5 fractional-oracle query with $(z, n)$ cast to rationals.
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328, Lemma 6, pp. 9 and 37

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Machine
import Definitions.Def_IntConeFPT_Instance
import Definitions.Def_IntConeFPT_Problem
import Definitions.Def_IntConeFPT_Residue

open OnlineCRS.Combine IntConeFPT

theorem IntConeFPT.lemma_6_prep_writer :
    let frame := fun (x y : List Sym) => x.flatMap (fun s => [(0 : Sym), s]) ++ 1 :: y
    ∃ C : ℕ, ∃ P : Machine, ∀ I : Instance, I.Valid →
      ∀ (t : Fin I.τ) (r : Residue I.d) (z : Fin I.d → ℤ) (w : Fin I.k → ℚ) (n : ℕ),
        1 ≤ n →
        let inp := encLocal I t r ++ encIntVec z ++ encVec w ++ encNat n ++ [3]
        let ctx := encNat I.d ++ [3] ++ encNat I.k ++ [3] ++ encResidue r ++ encIntVec z ++ encNat n ++ [3]
        let inp5 := encLocal I t r ++ encVec (fun i => (z i : ℚ)) ++ encVec w ++ encRat (n : ℚ) ++ [3]
        RunsWithin P inp (frame ctx inp5) (((inp.length : ℝ) + 2) ^ C) := by sorry
