-- Prove2me | Theorems.Thm_IntConeFPT_fiber_vertex_encoding_bound
-- name    : IntConeFPT.fiber_vertex_encoding_bound
-- status  : Proved
-- author  : @ohnesorgefelix
-- created : 2026-11-26T14:06:27.938687+00:00
-- url     : https://prove2.me/theorems/dff9a7da-83df-43a0-959c-3735c757ab71
-- title:
--   Fiber vertices have polynomial encoding length
-- statement:
--   Recall the set of fiber vertices of type $t$ and residue $r$ (§3, p.8):
--
--   $$V_r^{(t)}=\{(x,u)\in S_r^{(t)} : u \text{ is a vertex of the fiber } \{u'\in\mathbb R^k:(x,u')\in P^{(t)}\}\}.$$
--
--   **Statement.** There is a constant $C$ such that for every valid instance $I$, type $t$, residue $r$, integer vector $x\in\mathbb Z^d$ and rational vector $u\in\mathbb Q^k$ with $(x,u)\in V_r^{(t)}$,
--
--   $$|\mathrm{enc}(x,u)|\le |I|^C,$$
--
--   where $\mathrm{enc}(x,u)$ is `encGen x u` and $|I|$ is the length of `encInstance I`.
--
--   The reason: $P^{(t)}$ is a bounded rational polytope, so the integer part $x$ lies in a box whose bit size is polynomial in $|I|$, and a vertex $u$ of the fiber solves a nonsingular subsystem $B_S u=(c-Ax)_S$, so by Cramer's rule its entries have polynomially bounded encoding length. In the paper this is the statement that the point returned by Lemma 29 (and hence by the pricer of Lemma 5) has encoding length polynomial in $|I|$, independent of the objective.
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint), Lemma 29, p.33 ("The returned point can be chosen in V_r and has encoding length polynomial in |I|") and its use in the proof of Lemma 5, pp.35–36; V_r defined in §3, p.8

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

theorem fiber_vertex_encoding_bound :
    ∃ C : ℕ, ∀ I : Instance, I.Valid →
      ∀ (t : Fin I.τ) (r : Residue I.d) (x : Fin I.d → ℤ) (u : Fin I.k → ℚ),
        ratGen x u ∈ I.Vr t r → (encGen x u).length ≤ (encInstance I).length ^ C := by sorry

end IntConeFPT
