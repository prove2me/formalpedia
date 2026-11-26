-- Prove2me | Theorems.Thm_IntConeFPT_lemma_5_lex_lp
-- name    : IntConeFPT.lemma_5_lex_lp
-- status  : Open
-- author  : @ohnesorgefelix
-- created : 2026-11-26T13:24:45.564451+00:00
-- url     : https://prove2.me/theorems/ad0485ed-1a0a-4290-ab00-63518a5375fd
-- title:
--   Lemma 5, LP stage — $\Phi_r$, an optimal dual pair and a lexicographically optimal basic representation on $\le d+k+1$ fiber vertices
-- statement:
--   Fix a valid instance, a type $t$, a residue $r\in\{0,\dots,2^d-1\}^d$ with $S^{(t)}_r\neq\emptyset$, and a rational point $(z,w,n)\in C^{(t)}_r$. Let
--   $$p(x)=\Bigl\|\frac{x-r}{2^d}\Bigr\|_2^2$$
--   be the secondary objective of the proof of Lemma 5. There are an absolute constant $C$ and a deterministic algorithm that returns
--
--   1. the value $\varphi=\Phi^{(t)}_r(z,w,n)$;
--   2. a rational dual pair $(a^\star,b^\star)\in D^{(t)}_r$ with $\varphi=\langle a^\star,(z,w)\rangle+b^\star n$;
--   3. pairwise distinct rational fiber vertices $(x_i,u_i)\in V^{(t)}_r$, at most $d+k+1$ of them, with positive rational multiplicities $\theta_i$, such that
--   $$\sum_i\theta_i(x_i,u_i)=(z,w),\qquad \sum_i\theta_i=n,\qquad \sum_i\theta_i f^{(t)}(x_i)=\varphi;$$
--   4. this representation is lexicographically optimal over all of $S^{(t)}_r$: every fractional representation $\theta'$ of $(z,w,n)$ by generators of $S^{(t)}_r$ whose cost is at most $\varphi$ satisfies $\sum_i\theta_ip(x_i)\le\sum_g\theta'_g\,p(g_x)$.
--
--   The total output length is at most $L^C$, and the algorithm runs within $2^{Cd^2\log_2(d+1)}\cdot L^C$ steps, where $L$ is the length of the encoded input $(I,t,r,z,w,n)$. Its output is the encoding of $d$ and $k$ followed by the encoded triple.
--
--   This is the linear-programming part of the proof of Lemma 5 (p.35). The dual (3.1b) is solved by the ellipsoid method of Grötschel–Lovász–Schrijver, with the integer pricing of Lemma 29 as the strong separation oracle. A second run with the perturbed cost $f+\varepsilon p$ produces an optimal basic representation that minimizes $p$ among the minimum-cost representations. The remaining steps of Lemma 5, merging generators with equal integer coordinates and the parity bound $2^d$, take this output as input.
--
--   **Formalization Note.** The machine model, the encodings and the reading of $O(\cdot)$ are those of Lemma 5 (`Machine`, `RunsWithin`, `oracleBound`, `encOracle`). The output is prefixed by `encNat d ++ [3] ++ encNat k ++ [3]`, which is a prefix of the input, so that a subsequent machine can parse the generator list. The lexicographic optimality is stated against all real fractional representations on $S^{(t)}_r$, as in the proof ("minimizing the two objectives lexicographically over the finite LP is equivalent to doing so over all fractional representations on $S_r$").
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint), proof of Lemma 5, Section B.1, pp.35–36 (the ellipsoid/GLS procedure with the Lemma 29 separation oracle, and the lexicographic perturbation $\tilde f=f+\varepsilon p$)

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

theorem lemma_5_lex_lp :
    ∃ C : ℕ, ∃ M : Machine, ∀ I : Instance, I.Valid →
      ∀ (t : Fin I.τ) (r : Residue I.d) (z : Fin I.d → ℚ) (w : Fin I.k → ℚ) (n : ℚ),
        (I.Sr t r).Nonempty →
        ((ratPair z w).1, (ratPair z w).2, (n : ℝ)) ∈ I.Cr t r →
        let inp := encLocal I t r ++ encVec z ++ encVec w ++ encRat n ++ [3]
        let p : (Fin I.d → ℝ) → ℝ := fun x => ∑ i, ((x i - ((r i : ℕ) : ℝ)) / 2 ^ I.d) ^ 2
        ∃ o : ℚ × ((Fin I.d → ℚ) × (Fin I.k → ℚ)) × ℚ × List ((Fin I.d → ℤ) × (Fin I.k → ℚ) × ℚ),
          ((o.1 : ℝ) : EReal) = I.Phi t r ((ratPair z w).1, (ratPair z w).2, (n : ℝ)) ∧
          (ratPair o.2.1.1 o.2.1.2, (o.2.2.1 : ℝ)) ∈ I.Dr t r ∧
          (o.1 : ℝ) = pairing (ratPair o.2.1.1 o.2.1.2) (ratPair z w) + (o.2.2.1 : ℝ) * n ∧
          o.2.2.2.length ≤ I.d + I.k + 1 ∧
          (o.2.2.2.map fun e => (e.1, e.2.1)).Nodup ∧
          (∀ e ∈ o.2.2.2, ratGen e.1 e.2.1 ∈ I.Vr t r ∧ 0 < e.2.2) ∧
          (o.2.2.2.map fun e => (e.2.2 : ℝ) • (ratGen e.1 e.2.1).toReal).sum = ratPair z w ∧
          (o.2.2.2.map fun e => (e.2.2 : ℝ)).sum = n ∧
          (o.2.2.2.map fun e => (e.2.2 : ℝ) * I.f t (fun i => (e.1 i : ℝ))).sum = o.1 ∧
          (∀ θ : Gen I.d I.k →₀ ℝ,
            IsFracRep (I.Sr t r) θ ((ratPair z w).1, (ratPair z w).2, (n : ℝ)) →
            fracCost (I.f t) θ ≤ o.1 →
            (o.2.2.2.map fun e => (e.2.2 : ℝ) * p (fun i => (e.1 i : ℝ))).sum ≤ fracCost p θ) ∧
          (encOracle o).length ≤ inp.length ^ C ∧
          RunsWithin M inp (encNat I.d ++ [3] ++ encNat I.k ++ [3] ++ encOracle o)
            (oracleBound C I.d inp.length) := by sorry

end IntConeFPT
