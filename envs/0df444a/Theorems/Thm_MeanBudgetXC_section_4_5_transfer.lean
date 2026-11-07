-- Prove2me | Theorems.Thm_MeanBudgetXC_section_4_5_transfer
-- name    : MeanBudgetXC.section_4_5_transfer
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:44:04.09873+00:00
-- url     : https://prove2.me/theorems/ad4cb26b-d3fc-4ab8-ab7a-02e34215f036
-- title:
--   Section 4.5 — transfer to the full pair projection, and the $3^N$ upper bound
-- statement:
--   1. Let $Q$ be the host graph of Section 4.3 on $N=8n_0+t\ell+2c+n_{\mathrm{iso}}$ vertices with a triangle-free padding graph $T$, $d=4n_0+v\ell+c\ge3$ and $\Delta(Q)\le d-1$. For every integer $a\ge2$,
--   $$\mathrm{xc}(P^{(a)}_{N,d})+|E|+1\ge\mathrm{xc}(\mathrm{COR}(n_0)),$$
--   and for every $B>2$,
--   $$\mathrm{xc}(P^{(a;B)}_{N,d})+|E|+1\ge\mathrm{xc}(\mathrm{COR}(n_0)).$$
--   2. Keeping explicit local probabilities for all contexts gives at most $\sum_{S\subseteq[N]}2^{|S|}=3^N$ nonnegativity inequalities, and one more for the mean budget. So $P^{(a)}_{N,d}$ and $P^{(a;B)}_{N,d}$ have extended formulations with at most $3^N+1$ inequalities.
--
--   The first clause transfers the lower bound to the pair bodies themselves, and the second gives the matching upper bound.
--
--   **Formalization Note** The bodies of clause 1 live on `Fin N` while the host lives on its structured vertex type with $N$ elements, so clause 1 includes the relabelling through a bijection between them.
--
--   Differences from the source:
--   - generalization: the host at the parameters (15), for all sufficiently large $N$ → every host with a triangle-free $T$, $d=4n_0+v\ell+c\ge3$ and $\Delta(Q)\le d-1$; reason: these are the conditions the argument uses, and they hold at (15) for large $N$ by Section 4.3 and Appendix C.1
--   - generalization: the upper bound at $d=\lfloor\theta N\rfloor$, $a\ge2$, $B>2$ → every finite vertex type and every $d$, $a$, $B$; reason: the counting argument uses none of these restrictions; the paper's case is a special case
--   - encoding: $\mathrm{COR}(n_0)$ in the coordinates $(z_i)_i$ and $(z_iz_j)_{i<j}$ → the platform's `corPolytope` in $n_0\times n_0$ matrix coordinates; reason: the two are linearly isomorphic, so they have the same extension complexity
--   - encoding: an upper bound on $\mathrm{xc}$ → existence of an extended formulation of size at most $3^N+1$; reason: the platform's `extensionComplexity` is an infimum in $\mathbb N$, and this form also asserts that a formulation exists
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 4.5, p.21

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_ExtensionComplexity_TSP_CutCor
import Definitions.Def_MeanBudgetXC_budgetBody
import Definitions.Def_MeanBudgetXC_hostGraph

namespace MeanBudgetXC

open ExtensionComplexity.TSP

/-- **Section 4.5, transfer to the full pair projection and the matching upper bound**
(Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 4.5, p.21).
1. For the host `Q` of Section 4.3 on `N = 8n₀ + tℓ + 2c + n_iso` vertices with a triangle-free
   padding graph `T`, `d = 4n₀ + vℓ + c ≥ 3` and `Δ(Q) ≤ d − 1`, for every integer `a ≥ 2`:
   `xc(P^{(a)}_{N,d}) + |E| + 1 ≥ xc(COR(n₀))` and, for every `B > 2`,
   `xc(P^{(a;B)}_{N,d}) + |E| + 1 ≥ xc(COR(n₀))`.
2. Keeping explicit local probabilities for all contexts gives formulations with at most
   `∑_{S ⊆ [N]} 2^{|S|} = 3^N` nonnegativity inequalities plus one mean-budget row:
   `P^{(a)}_{N,d}` and `P^{(a;B)}_{N,d}` have extended formulations with at most `3^N + 1`
   inequalities, for every `N, d, a` and `B`.

**Formalization Note** Clause 1 is stated for every host satisfying the hypotheses that the
paper's argument uses (Lemma 4.1 needs `3 ≤ d ≤ N`, `Q` triangle-free and `Δ(Q) ≤ d − 1`; `d ≤ N`
follows from `v ≤ t`); the paper applies it at the parameters (15) of Section 4.2, where they hold
for all sufficiently large `N` (Section 4.3 and Appendix C.1). The bodies live on `Fin N`, as in
the goal, while the host lives on its structured vertex type `HostV`, which has `N` elements; the
transfer through a bijection `HostV ≃ Fin N` is part of this statement. `COR(n₀)` is the platform's
`corPolytope` (linearly isomorphic to the paper's, same extension complexity). Clause 2's upper
bounds are existence of an extended formulation, not a bound on the infimum, and clause 2 holds
on every finite vertex type. -/
theorem section_4_5_transfer.{u} :
    (∀ (n₀ t ℓ c niso N d a : ℕ) (T : SimpleGraph (Fin t)) [DecidableRel T.Adj],
      T.CliqueFree 3 → N = 8 * n₀ + t * ℓ + 2 * c + niso →
      d = 4 * n₀ + T.vertexCoverNum.toNat * ℓ + c → 3 ≤ d →
      (hostGraph n₀ t ℓ c niso T).maxDegree ≤ d - 1 → 2 ≤ a →
        extensionComplexity (corPolytope n₀) ≤
            extensionComplexity (pairBody (Fin N) d a) +
              (hostGraph n₀ t ℓ c niso T).edgeFinset.card + 1 ∧
          ∀ B : ℝ, 2 < B →
            extensionComplexity (corPolytope n₀) ≤
              extensionComplexity (budgetBody (Fin N) d a B) +
                (hostGraph n₀ t ℓ c niso T).edgeFinset.card + 1) ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (d a : ℕ) (B : ℝ),
        (∃ r ≤ 3 ^ Fintype.card V + 1, IsEFOfSize (pairBody V d a) r) ∧
          ∃ r ≤ 3 ^ Fintype.card V + 1, IsEFOfSize (budgetBody V d a B) r := by sorry

end MeanBudgetXC
