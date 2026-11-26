-- Prove2me | Theorems.Thm_IntConeFPT_lemma_5_pricer
-- name    : IntConeFPT.lemma_5_pricer
-- status  : Open
-- author  : @ohnesorgefelix
-- created : 2026-11-26T13:41:26.017762+00:00
-- url     : https://prove2.me/theorems/9d8c01e2-200b-40dc-be54-29e1b0b7baa4
-- title:
--   Lemma 5, separation oracle — perturbed integer pricing with cost values, from Lemma 29
-- statement:
--   Let $I$ be a valid instance, $t$ a type and $r$ a residue with $S^{(t)}_r\ne\emptyset$, and let
--   $$p(x)=\Bigl\|\frac{x-r}{2^d}\Bigr\|_2^2 .$$
--   There are a constant $C$ and a deterministic algorithm that, given $(I,t,r)$, a rational $\varepsilon\ge0$ and $a=(a_x,a_u)\in\mathbb Q^d\times\mathbb Q^k$, returns a rational fiber vertex $(x,u)\in V^{(t)}_r$ together with the values $f^{(t)}(x)$ and $p(x)$, such that
--   $$
--   f^{(t)}(x)+\varepsilon p(x)-\langle a,(x,u)\rangle\ \le\ f^{(t)}(x')+\varepsilon p(x')-\langle a,(x',u')\rangle\qquad\text{for all }(x',u')\in S^{(t)}_r .
--   $$
--   The answer has encoding length at most $|\mathrm{enc}(I,t,r)|^C$ (independent of $\varepsilon$ and $a$), and the algorithm halts within $2^{Cd^2\log_2(d+1)}\cdot L^C$ steps, where $L$ is the length of the input.
--
--   This is the strong separation oracle for the dual (3.1b) used in the proof of Lemma 5, for both the original cost ($\varepsilon=0$) and the perturbed cost $\tilde f=f+\varepsilon p$. It follows from Lemma 29 applied to the instance whose cost polynomial is $f^{(t)}+\varepsilon p$, which is again convex, together with exact evaluation of $f^{(t)}$ and $p$ at the returned integer point.
--
--   **Formalization Note.** The input is `encLocal I t r ++ encRat ε ++ [3] ++ encVec a_x ++ encVec a_u`, and the output is `encGen x u ++ encRat (f x) ++ encRat (p x) ++ [3]`. This is the oracle format of `IntConeFPT.lex_column_generation` with context `encLocal I t r`.
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint), proof of Lemma 5, Section B.1, pp.35–36: the separation oracle (B.1) via Lemma 29, also for the perturbed cost f̃ = f + εp ("The quadratic p is convex, so f̃ satisfies the discrete Jensen inequality … all pricing and LP operations for the perturbed cost have the same running-time bound")

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

theorem lemma_5_pricer :
    ∃ C : ℕ, ∃ P : Machine, ∀ I : Instance, I.Valid →
      ∀ (t : Fin I.τ) (r : Residue I.d), (I.Sr t r).Nonempty →
      ∀ (ε : ℚ), 0 ≤ ε → ∀ (ax : Fin I.d → ℚ) (au : Fin I.k → ℚ),
        let p : (Fin I.d → ℝ) → ℝ := fun x => ∑ i, ((x i - ((r i : ℕ) : ℝ)) / 2 ^ I.d) ^ 2
        let q := encLocal I t r ++ encRat ε ++ [3] ++ encVec ax ++ encVec au
        ∃ (x : Fin I.d → ℤ) (u : Fin I.k → ℚ) (cq sq : ℚ),
          ratGen x u ∈ I.Vr t r ∧ (cq : ℝ) = I.f t (fun i => (x i : ℝ)) ∧
          (sq : ℝ) = p (fun i => (x i : ℝ)) ∧
          (∀ g ∈ I.Sr t r, (cq : ℝ) + (ε : ℝ) * sq - pairing (ratPair ax au) (ratGen x u).toReal ≤
            I.f t (fun i => (g.1 i : ℝ)) + (ε : ℝ) * p (fun i => (g.1 i : ℝ)) -
              pairing (ratPair ax au) g.toReal) ∧
          (encGen x u ++ encRat cq ++ encRat sq ++ [3]).length ≤ (encLocal I t r).length ^ C ∧
          RunsWithin P q (encGen x u ++ encRat cq ++ encRat sq ++ [3])
            (oracleBound C I.d q.length) := by sorry

end IntConeFPT
