-- Prove2me | Theorems.Thm_GreedNorm_proposition_3_9
-- name    : GreedNorm.proposition_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:46:55.710194+00:00
-- url     : https://prove2.me/theorems/41608e1e-73fd-49ce-8672-2b1ad8c70414
-- title:
--   Proposition 3.9 — validity is a partition matroid and $t$-boundedness a nested matroid on configurations
-- statement:
--   Fix $\epsilon>0$, a threshold vector $t$ and load functions $\mathrm{load}_i$, and let $X_\ell=\{(i,S)\in V:\mathrm{load}_i(S)>t_\ell\}$ for $\ell\in\mathrm{POS}$. Then:
--
--   1. there is a matroid on the ground set $V=[m]\times2^U$ whose independent sets are exactly the valid configuration sets (the partition matroid whose parts are the types, each with capacity $1$);
--   2. the sets $X_\ell$ form a chain: $\ell\le\ell'$ in $\mathrm{POS}$ implies $X_\ell\subseteq X_{\ell'}$;
--   3. $\mathcal A$ is $t$-bounded if and only if $|\mathcal A\cap X_\ell|\le \ell-1$ for every $\ell\in\mathrm{POS}$;
--   4. there is a matroid on $V$ whose independent sets are exactly the $t$-bounded configuration sets.
--
--   Items 2–4 say that $t$-boundedness is a nested matroid constraint (chain $X_\ell$, capacities $\ell-1$). Together the two constraints make ThreshBudgCovConfig a coverage maximization over the intersection of $p=2$ matroids.
--
--   Differences from the source:
--   - reading: the t-bounded and validity constraints are nested matroid and partition matroid constraints with ground set V → existence of Mathlib matroids on V (ground set univ) with exactly the valid, resp. t-bounded, sets independent, plus the chain X_ℓ ⊆ X_ℓ' and the |A ∩ X_ℓ| ≤ ℓ − 1 form of footnote 3; reason: footnote 3 defines a nested matroid by a chain and capacities; the partition form of validity is its definition (parts = types, capacity 1)
--   - encoding: configurations (i, S), i ∈ [m], S ⊆ U; configuration sets → Fin m × Finset U (types 0-based); Finset of configurations; reason: Lean convention; same instances
--   - generalization: load functions load_i : 2^U → R_{≥0} (Definition 1.2) → arbitrary real-valued load : Fin m → Finset U → ℝ; reason: neither matroid property uses the sign of the loads; nonnegative loads are among these, so the statement specializes to the source's
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Proposition 3.9, p.8 (PDF 10); nested matroid, footnote 3, p.5 (PDF 7)

import Mathlib
import Definitions.Def_GreedNorm_POS
import Definitions.Def_GreedNorm_IsThreshold
import Definitions.Def_GreedNorm_IsValidConf
import Definitions.Def_GreedNorm_IsTBoundedConf

namespace GreedNorm

/-- **Proposition 3.9: validity is a partition matroid and `t`-boundedness a nested matroid on
the configurations.**
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Proposition 3.9, p.8 (PDF 10): "The t-bounded and validity constraints are nested matroid
and partition matroid constraints, respectively, with ground set V." Nested matroid as in
footnote 3, p.5 (PDF 7): "a collection of subsets X1, . . . , Xk such that X1 ⊆ · · · ⊆ Xk ⊆ X,
and non-negative integers ℓ1, . . . , ℓk. A subset I ⊆ X is defined to be independent if, for all
1 ≤ i ≤ k, we have that |I ∩ Xi| ≤ ℓi."

For a threshold vector `t` and any load functions, with `X_ℓ = {(i,S) : load_i(S) > t_ℓ}`:
1. there is a matroid on `V = [m] × 2^U` whose independent sets are exactly the valid
   configuration sets (the partition matroid with parts the types and capacity 1);
2. the sets `X_ℓ`, `ℓ ∈ POS`, form a chain: `ℓ ≤ ℓ'` gives `X_ℓ ⊆ X_ℓ'`;
3. `A` is `t`-bounded iff `|A ∩ X_ℓ| ≤ ℓ − 1` for every `ℓ ∈ POS`;
4. there is a matroid on `V` whose independent sets are exactly the `t`-bounded configuration
   sets.

**Formalization Note** Matroids are Mathlib `Matroid (Fin m × Finset U)` with ground set
`univ`; configuration sets are `Finset`s. No hypothesis on the loads is needed. -/
theorem proposition_3_9 {U : Type} [Fintype U] [DecidableEq U] (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (t : ℕ → ℝ) (ht : IsThreshold m ε t) (load : Fin m → Finset U → ℝ) :
    (∃ M : Matroid (Fin m × Finset U), M.E = Set.univ ∧
        ∀ A : Finset (Fin m × Finset U), M.Indep (↑A : Set (Fin m × Finset U)) ↔ IsValidConf A) ∧
      (∀ ℓ ∈ POS m ε, ∀ ℓ' ∈ POS m ε, ℓ ≤ ℓ' →
        Finset.univ.filter (fun c : Fin m × Finset U => t ℓ < load c.1 c.2) ⊆
          Finset.univ.filter (fun c : Fin m × Finset U => t ℓ' < load c.1 c.2)) ∧
      (∀ A : Finset (Fin m × Finset U), IsTBoundedConf ε load t A ↔
        ∀ ℓ ∈ POS m ε,
          (A ∩ Finset.univ.filter (fun c : Fin m × Finset U => t ℓ < load c.1 c.2)).card ≤ ℓ - 1) ∧
      (∃ M : Matroid (Fin m × Finset U), M.E = Set.univ ∧
        ∀ A : Finset (Fin m × Finset U),
          M.Indep (↑A : Set (Fin m × Finset U)) ↔ IsTBoundedConf ε load t A) := by sorry

end GreedNorm
