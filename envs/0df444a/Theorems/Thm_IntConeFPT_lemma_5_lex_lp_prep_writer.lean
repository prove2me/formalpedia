-- Prove2me | Theorems.Thm_IntConeFPT_lemma_5_lex_lp_prep_writer
-- name    : IntConeFPT.lemma_5_lex_lp_prep_writer
-- status  : Proved
-- author  : @ohnesorgefelix
-- created : 2026-11-26T13:41:33.840303+00:00
-- url     : https://prove2.me/theorems/e5e5406c-bf60-4d90-a5bd-f9115764600f
-- title:
--   Lemma 5, input writer — move the query before the instance and prefix the dimensions
-- statement:
--   There are a constant $C$ and a deterministic algorithm that, for every valid instance $I$, type $t$, residue $r$ and rational query $(z,w,n)$, rewrites the input
--   $$\mathrm{enc}(I,t,r)\ \mathrm{enc}(z)\ \mathrm{enc}(w)\ \mathrm{enc}(n)$$
--   into
--   $$\mathrm{enc}(d)\ \mathrm{enc}(k)\ \mathrm{enc}(z)\ \mathrm{enc}(w)\ \mathrm{enc}(n)\ \mathrm{enc}(I,t,r)$$
--   within $(L+2)^C$ steps, where $L$ is the input length.
--
--   This is the format change between the call of Lemma 5's linear-programming stage and the generic column-generation procedure `IntConeFPT.lex_column_generation`. That procedure reads the dimensions and the query first and treats the instance as an opaque context word passed to the pricing oracle. The algorithm parses the self-delimiting encoding of $(I,t,r)$ to locate the query.
--
--   **Formalization Note.** Input `encLocal I t r ++ encVec z ++ encVec w ++ encRat n ++ [3]`, output `encNat d ++ [3] ++ encNat k ++ [3] ++ encVec z ++ encVec w ++ encRat n ++ [3] ++ encLocal I t r`, in the mission's `Machine`/`RunsWithin` model.
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint), proof of Lemma 5, Section B.1, p.35 (bookkeeping between the oracle input (I, t, r, z, w, n) and the LP procedure)

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
import Definitions.Def_IntConeFPT_Formulation

open OnlineCRS.Combine

namespace IntConeFPT

theorem lemma_5_lex_lp_prep_writer :
    ∃ C : ℕ, ∃ W : Machine, ∀ I : Instance, I.Valid →
      ∀ (t : Fin I.τ) (r : Residue I.d) (z : Fin I.d → ℚ) (w : Fin I.k → ℚ) (n : ℚ),
        let inp := encLocal I t r ++ encVec z ++ encVec w ++ encRat n ++ [3]
        RunsWithin W inp
          (encNat I.d ++ [3] ++ encNat I.k ++ [3] ++ encVec z ++ encVec w ++ encRat n ++ [3] ++
            encLocal I t r)
          (((inp.length : ℝ) + 2) ^ C) := by sorry

end IntConeFPT
