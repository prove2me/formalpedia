-- Prove2me | Theorems.Thm_IntConeFPT_lemma_5_pricer_perturb_writer
-- name    : IntConeFPT.lemma_5_pricer_perturb_writer
-- status  : Open
-- author  : @ohnesorgefelix
-- created : 2026-11-26T14:06:27.138204+00:00
-- url     : https://prove2.me/theorems/f8c10f03-11d8-5120-8f19-7f0be81636a5
-- title:
--   Lemma 5 pricer: writing the perturbed instance with cost $f+\varepsilon p$
-- statement:
--   In the proof of Lemma 5 the pricing step minimizes the perturbed cost $f+\varepsilon p$ over a residue class $S_r$, where
--
--   $$p(x)=\sum_{i=1}^{d}\left(\frac{x_i-r_i}{2^d}\right)^2 .$$
--
--   Since $f+\varepsilon p$ is again an explicitly given convex polynomial, the paper applies Lemma 29 (integer pricing) to the instance $I'$ that agrees with $I$ except that each cost polynomial $f^{(t)}$ is replaced by $f^{(t)}+\varepsilon p$. This statement asserts that $I'$ can be written down in polynomial time.
--
--   **Statement.** There are a constant $C$ and a machine $W$ such that for every valid instance $I$, type $t$, residue $r\in\{0,\dots,2^d-1\}^d$, rational $\varepsilon\ge 0$ and rational vectors $a_x\in\mathbb Q^d$, $a_u\in\mathbb Q^k$ the following holds. Let $q=\mathrm{enc}(I,t,r)\,\varepsilon\,a_x\,a_u$ be the input (`encLocal I t r ++ encRat ε ++ [3] ++ encVec ax ++ encVec au`). Then there exist degree bounds $D_{t'}$ and rational coefficient vectors $c_{t'}$ (on the dense monomial list `monomials d (D t')`) such that the instance $I'$ obtained from $I$ by replacing `deg` with $D$ and `coeff` with $c$ satisfies
--
--   1. $f'^{(t')}(x)=f^{(t')}(x)+\varepsilon\,p(x)$ for every type $t'$ and every $x\in\mathbb R^d$ (with the same $r$ for all types);
--   2. $|\mathrm{enc}(I',t,r)|\le (|q|+2)^C$;
--   3. $W$ maps $q$ within $(|q|+2)^C$ steps to the threaded word consisting of $\mathrm{enc}(I,t,r)$ written in the context format of `runsWithin_thread` (each symbol $s$ as $0\,s$), the marker $1$, and then $\mathrm{enc}(I',t,r)\,a_x\,a_u$, i.e. the input of Lemma 29 for $I'$.
--
--   All other data of $I$ (dimensions, polytopes $P^{(t)}$, $Q$, $A$) are unchanged, so $S_r$ and $V_r$ are the same for $I$ and $I'$. A natural choice is $D_{t'}=\max(\deg f^{(t')},2)$.
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

theorem lemma_5_pricer_perturb_writer :
    ∃ C : ℕ, ∃ W : Machine, ∀ I : Instance, I.Valid →
      ∀ (t : Fin I.τ) (r : Residue I.d) (ε : ℚ), 0 ≤ ε →
      ∀ (ax : Fin I.d → ℚ) (au : Fin I.k → ℚ),
        let p : (Fin I.d → ℝ) → ℝ := fun x => ∑ i, ((x i - ((r i : ℕ) : ℝ)) / 2 ^ I.d) ^ 2
        let q := encLocal I t r ++ encRat ε ++ [3] ++ encVec ax ++ encVec au
        ∃ (D : Fin I.τ → ℕ) (c : (t' : Fin I.τ) → Fin (monomials I.d (D t')).length → ℚ),
          (∀ (t' : Fin I.τ) (x : Fin I.d → ℝ),
            ({ I with deg := D, coeff := c } : Instance).f t' x = I.f t' x + (ε : ℝ) * p x) ∧
          (encLocal ({ I with deg := D, coeff := c } : Instance) t r).length ≤
            (q.length + 2) ^ C ∧
          RunsWithin W q
            ((encLocal I t r).flatMap (fun s => [(0 : Sym), s]) ++
              1 :: (encLocal ({ I with deg := D, coeff := c } : Instance) t r ++
                encVec ax ++ encVec au))
            (((q.length : ℝ) + 2) ^ C) := by sorry

end IntConeFPT
