-- Prove2me | Theorems.Thm_IntConeFPT_lemma_5_merge_support
-- name    : IntConeFPT.lemma_5_merge_support
-- status  : Proved
-- author  : @ohnesorgefelix
-- created : 2026-11-26T13:25:13.910471+00:00
-- url     : https://prove2.me/theorems/eb884d17-832b-4349-9042-a4a603933a20
-- title:
--   Lemma 5, support bound — merging a lexicographically optimal representation leaves at most $2^d$ generators in $S_r$
-- statement:
--   Let $I$ be a valid instance, $t$ a type and $r\in\{0,\dots,2^d-1\}^d$ a residue. Let $L=((x_i,u_i,\theta_i))_i$ be a list of generators $(x_i,u_i)\in S^{(t)}_r$, $u_i\in\mathbb Q^k$, with positive rational multiplicities $\theta_i$. Suppose that $L$ represents $(z,w,n)$ at cost $\varphi$:
--   $$\sum_i\theta_i(x_i,u_i)=(z,w),\qquad \sum_i\theta_i=n,\qquad \sum_i\theta_if^{(t)}(x_i)=\varphi.$$
--   Suppose further that $L$ is lexicographically optimal for the secondary objective $p(x)=\|(x-r)/2^d\|_2^2$: every fractional representation $\theta'$ of $(z,w,n)$ on $S^{(t)}_r$ with cost at most $\varphi$ satisfies $\sum_i\theta_ip(x_i)\le\sum_g\theta'_gp(g_x)$. Then the merged list $L'=\mathrm{fracMerge}(L)$, which averages the continuous coordinates of entries with the same integer coordinates, satisfies
--
--   1. $|L'|\le 2^d$ and $|L'|\le|L|$;
--   2. the generators of $L'$ are pairwise distinct, lie in $S^{(t)}_r$, and have positive multiplicities;
--   3. $L'$ represents $(z,w,n)$ at the same cost $\varphi$.
--
--   This is the end of the proof of Lemma 5 (p.36). Averaging keeps every generator in $S^{(t)}_r$ by convexity of $P^{(t)}$, and it preserves the aggregate, the count and both objectives. If more than $2^d$ distinct integer coordinates remained, two of the normalized vectors $a_i=(x_i-r)/2^d$ would have the same parity. Their midpoint is a generator of $S^{(t)}_r$, and convexity of $f^{(t)}$ shows that shifting weight to it does not increase the cost. The secondary objective, however, drops by $\frac{\alpha}{2}\|a_i-a_j\|_2^2>0$, which contradicts lexicographic optimality.
--
--   **Formalization Note.** Aggregates and costs are compared in $\mathbb R$ via the casts used in Lemma 5. Lexicographic optimality is the hypothesis produced by `IntConeFPT.lemma_5_lex_lp`. The statement is pure mathematics; no machine is involved.
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint), proof of Lemma 5, Section B.1, pp.35–36 (merging and the midpoint/parity argument, p.36)

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
import Definitions.Def_IntConeFPT_fracMerge

open OnlineCRS.Combine

namespace IntConeFPT

theorem lemma_5_merge_support (I : Instance) (hI : I.Valid) (t : Fin I.τ) (r : Residue I.d)
    (z : Fin I.d → ℚ) (w : Fin I.k → ℚ) (n φ : ℚ)
    (L : List ((Fin I.d → ℤ) × (Fin I.k → ℚ) × ℚ))
    (hS : ∀ e ∈ L, ratGen e.1 e.2.1 ∈ I.Sr t r ∧ 0 < e.2.2)
    (hagg : (L.map fun e => (e.2.2 : ℝ) • (ratGen e.1 e.2.1).toReal).sum = ratPair z w)
    (hcnt : (L.map fun e => (e.2.2 : ℝ)).sum = n)
    (hcost : (L.map fun e => (e.2.2 : ℝ) * I.f t (fun i => (e.1 i : ℝ))).sum = φ)
    (hlex : ∀ θ : Gen I.d I.k →₀ ℝ,
      IsFracRep (I.Sr t r) θ ((ratPair z w).1, (ratPair z w).2, (n : ℝ)) →
      fracCost (I.f t) θ ≤ φ →
      (L.map fun e => (e.2.2 : ℝ) *
          ∑ i, (((e.1 i : ℝ) - ((r i : ℕ) : ℝ)) / 2 ^ I.d) ^ 2).sum ≤
        fracCost (fun x => ∑ i, ((x i - ((r i : ℕ) : ℝ)) / 2 ^ I.d) ^ 2) θ) :
    (fracMerge L).length ≤ 2 ^ I.d ∧ (fracMerge L).length ≤ L.length ∧
      ((fracMerge L).map fun e => (e.1, e.2.1)).Nodup ∧
      (∀ e ∈ fracMerge L, ratGen e.1 e.2.1 ∈ I.Sr t r ∧ 0 < e.2.2) ∧
      ((fracMerge L).map fun e => (e.2.2 : ℝ) • (ratGen e.1 e.2.1).toReal).sum = ratPair z w ∧
      ((fracMerge L).map fun e => (e.2.2 : ℝ)).sum = n ∧
      ((fracMerge L).map fun e => (e.2.2 : ℝ) * I.f t (fun i => (e.1 i : ℝ))).sum = φ := by sorry

end IntConeFPT
