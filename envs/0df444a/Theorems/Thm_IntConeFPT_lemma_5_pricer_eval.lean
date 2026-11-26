-- Prove2me | Theorems.Thm_IntConeFPT_lemma_5_pricer_eval
-- name    : IntConeFPT.lemma_5_pricer_eval
-- status  : Open
-- author  : @ohnesorgefelix
-- created : 2026-11-26T14:07:06.648804+00:00
-- url     : https://prove2.me/theorems/dda644a3-b988-4861-b2d7-04580b356245
-- title:
--   Lemma 5 pricer: evaluating $f(x)$ and $p(x)$ at an integer point
-- statement:
--   After the pricing call of Lemma 29 returns a generator $(x,u)$, the pricer of Lemma 5 reports the exact values $f^{(t)}(x)$ and $p(x)$, where
--
--   $$p(x)=\sum_{i=1}^{d}\left(\frac{x_i-r_i}{2^d}\right)^2 .$$
--
--   This statement asserts that both values can be computed exactly, in polynomial time and with polynomial encoding length.
--
--   **Statement.** There are a constant $C$ and a machine $E$ such that for every valid instance $I$, type $t$, residue $r$, integer vector $x\in\mathbb Z^d$ and rational vector $u\in\mathbb Q^k$ the following holds. Let the input be the threaded word made of $\mathrm{enc}(I,t,r)$ in the context format of `runsWithin_thread` (each symbol $s$ as $0\,s$), the marker $1$, and the pricing output `encPricing (some (x,u))` $=1\,\mathrm{enc}(x,u)$. Then there are rationals $c_q,s_q$ with
--
--   $$c_q=f^{(t)}(x),\qquad s_q=p(x),$$
--
--   $$|\mathrm{enc}(c_q)|+|\mathrm{enc}(s_q)|\le\bigl(|\mathrm{enc}(I,t,r)|+|\mathrm{enc}(x,u)|\bigr)^C,$$
--
--   and $E$ outputs $\mathrm{enc}(x,u)\,\mathrm{enc}(c_q)\,\mathrm{enc}(s_q)\,3$ within $(L+2)^C$ steps, $L$ the input length.
--
--   The bound holds because $f^{(t)}$ is given densely: the number of listed coefficients is at least $\deg f^{(t)}+1$ (as $d\ge1$), so $\deg f^{(t)}\le|I|$ and every monomial value $x^e$ has bit length at most $\deg f^{(t)}\cdot|\mathrm{enc}(x)|$.
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint), proof of Lemma 5, pp.35–36 (pricing over S_r with the perturbed cost f + εp via Lemma 29, p.33)

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

open OnlineCRS.Combine

namespace IntConeFPT

theorem lemma_5_pricer_eval :
    ∃ C : ℕ, ∃ E : Machine, ∀ I : Instance, I.Valid →
      ∀ (t : Fin I.τ) (r : Residue I.d) (x : Fin I.d → ℤ) (u : Fin I.k → ℚ),
        let p : (Fin I.d → ℝ) → ℝ := fun x => ∑ i, ((x i - ((r i : ℕ) : ℝ)) / 2 ^ I.d) ^ 2
        let inp := (encLocal I t r).flatMap (fun s => [(0 : Sym), s]) ++
          1 :: encPricing (some (x, u))
        ∃ cq sq : ℚ, (cq : ℝ) = I.f t (fun i => (x i : ℝ)) ∧
          (sq : ℝ) = p (fun i => (x i : ℝ)) ∧
          (encRat cq ++ encRat sq).length ≤
            ((encLocal I t r).length + (encGen x u).length) ^ C ∧
          RunsWithin E inp (encGen x u ++ encRat cq ++ encRat sq ++ [3])
            (((inp.length : ℝ) + 2) ^ C) := by sorry

end IntConeFPT
