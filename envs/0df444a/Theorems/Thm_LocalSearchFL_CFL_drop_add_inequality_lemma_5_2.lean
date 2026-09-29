-- Prove2me | Theorems.Thm_LocalSearchFL_CFL_drop_add_inequality_lemma_5_2
-- name    : LocalSearchFL.CFL.drop_add_inequality_lemma_5_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:22:07.135637+00:00
-- url     : https://prove2.me/theorems/d7612336-211e-4d97-8059-a142684f0ed2
-- title:
--   Lemma 5.2 — the drop-add inequality ⌈|N_S(U)|/u_{s'}⌉ f_{s'} + Σ |N_S(s)| c_{ss'} ≥ Σ f_s
-- statement:
--   Let $C$ be a nonempty finite set of clients and $F$ a set of facilities in a metric instance with distances $c$, integer capacities $u_i > 0$ and facility costs $f_i \ge 0$. Let $X$ be a locally optimum CFL solution for the neighbourhood (9), with open copies $s$ located at facilities $\mathrm{loc}(s)$ and client sets $N_X(s)$. Then for every set $U$ of copies of $X$ and every facility $s' \in F$,
--
--   $$\left\lceil \frac{|N_X(U)|}{u_{s'}} \right\rceil f_{s'} + \sum_{s \in U} |N_X(s)|\, c_{s s'} \ \ge\ \sum_{s \in U} f_s,$$
--
--   where $N_X(U) = \bigcup_{s\in U} N_X(s)$, $f_s = f_{\mathrm{loc}(s)}$ and $c_{ss'}$ is the distance between the facility $\mathrm{loc}(s)$ and $s'$.
--
--   The inequality records that closing the copies in $U$ and opening enough copies of $s'$ to absorb their clients does not decrease the cost. It is applied in the proof of Lemma 5.3 to the sets $T_o$ defined by a shortest-path flow.
--
--   **Formalization Note** The ceiling is `Nat.ceil` of the real quotient. The hypothesis that there is at least one client is added: without clients, a single idle copy of a facility with $f = 1$, $u = 1$ is locally optimum (its neighbours cost $2$ or $1$), and $U = \{$that copy$\}$ gives $0 \ge 1$.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 559, Lemma 5.2

import Mathlib
import Definitions.Def_LocalSearchFL_CFL_IsCFLLocalOpt

namespace LocalSearchFL.CFL

/-- **Lemma 5.2**, p. 559: in a locally optimum CFL solution `X` (at least one client), for
every set `U` of copies of `X` and every facility `s'`,
`⌈|N_X(U)| / u_{s'}⌉ · f_{s'} + ∑_{s ∈ U} |N_X(s)| · c_{s s'} ≥ ∑_{s ∈ U} f_s`,
where `c_{s s'}` is the distance between the facility of copy `s` and `s'`. -/
theorem drop_add_inequality_lemma_5_2 {Cl Fa : Type} [Fintype Cl] [Nonempty Cl]
    (I : MetricInstance Cl Fa) (u : Fa → ℕ) (hu : ∀ i, 0 < u i) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (X : CFLSol Cl Fa u) (hX : IsCFLLocalOpt I f X) (U : Finset (Fin X.n)) (s' : Fa) :
    ∑ s ∈ U, f (X.loc s) ≤
      (⌈((X.nbhdSet U).card : ℝ) / (u s' : ℝ)⌉₊ : ℝ) * f s' +
        ∑ s ∈ U, ((X.nbhd s).card : ℝ) * I.cf (X.loc s) s' := by sorry

end LocalSearchFL.CFL
