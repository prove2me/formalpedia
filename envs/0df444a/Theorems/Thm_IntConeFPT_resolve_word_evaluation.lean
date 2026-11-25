-- Prove2me | Theorems.Thm_IntConeFPT_resolve_word_evaluation
-- name    : IntConeFPT.resolve_word_evaluation
-- status  : Open
-- author  : @ohnesorgefelix
-- created : 2026-11-25T11:52:28.928074+00:00
-- url     : https://prove2.me/theorems/f08cace6-4c98-4e5e-8a29-7d814c3d96d9
-- title:
--   Polynomial-time resolution of two encoded solver responses
-- statement:
--   Given the encoded instance and the two encoded responses, output their prescribed combination in polynomial time. The inputs need not be correct certificates. On the branches that require it, evaluate the dense rational polynomial cost of the homogeneous certificate exactly and test its sign; the other branches use only the response tags. The input is framed with the two-symbol context encoding used for subroutine calls.
-- source:
--   Jansen, Ohnesorge and Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, https://arxiv.org/abs/2609.31328, §3.6, proof of Theorem 1, p.18, and formula (3.4).

import Definitions.Def_IntConeFPT_Homogenized
import Definitions.Def_IntConeFPT_Machine
open OnlineCRS.Combine IntConeFPT

theorem IntConeFPT.resolve_word_evaluation :
    let frame := fun (x y : List Sym) => x.flatMap (fun s => [(0 : Sym),s]) ++ 1::y
    ∃ d : ℕ, ∃ P : Machine, ∀ I : Instance, I.Valid →
      ∀ (a : Output I) (b : Output (homInstance I)),
        let w := frame (frame (encInstance I) (encOutput a)) (encOutput b)
        RunsWithin P w (encOutput (resolveOutput I a b)) ((w.length + 2 : ℝ)^d) := by sorry
