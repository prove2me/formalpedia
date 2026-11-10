-- Prove2me | Theorems.Thm_GreedNorm_prune_configuration_set
-- name    : GreedNorm.prune_configuration_set
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:46:14.933146+00:00
-- url     : https://prove2.me/theorems/61b25f91-0565-4f06-ad71-541da9b24f05
-- title:
--   §3.2 — pruning a valid configuration set to a disjoint one with no larger loads
-- statement:
--   Let the load functions be monotone and let $\mathcal A$ be a valid configuration set. Then there are sets $S'_{(i,S)}\subseteq S$, one for each $(i,S)\in\mathcal A$, pairwise disjoint, such that $\mathcal A'=\{(i,S'_{(i,S)}):(i,S)\in\mathcal A\}$
--
--   1. is valid and covers the same elements, $\mathrm{cov}(\mathcal A')=\mathrm{cov}(\mathcal A)$;
--   2. has $\mathrm{load}_i(S'_{(i,S)})\le\mathrm{load}_i(S)$ for each $(i,S)\in\mathcal A$;
--   3. is $t$-bounded for every threshold vector $t$ for which $\mathcal A$ is.
--
--   Thus each element is contained in at most one configuration of $\mathcal A'$, and $\mathcal A'$ defines a partial assignment covering $\mathrm{cov}(\mathcal A)$.
--
--   Differences from the source:
--   - generalization: A′ valid, each element in at most one configuration, load(A′) ≤ load(A) → additionally π(i,S) ⊆ S, cov(A′) = cov(A), and t-boundedness preserved for every t; reason: these are what 'pruning' means and what its use requires; the source's three properties are among the conclusions
--   - encoding: load(A′) ≤ load(A) → load_i(π(i,S)) ≤ load_i(S) for every (i, S) ∈ A; reason: the load vectors of A and A′ are compared configuration by configuration, which is the coordinatewise order
--   - generalization: monotone load functions load_i : 2^U → R_{≥0} (Definition 1.2) → monotone real-valued load : Fin m → Finset U → ℝ; reason: pruning uses only monotonicity; nonnegative loads are among these
--   - encoding: configurations (i, S), i ∈ [m], S ⊆ U; configuration sets → Fin m × Finset U (types 0-based); Finset of configurations; reason: Lean convention; same instances
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), §3.2, p.8 (PDF 10)

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn
import Definitions.Def_GreedNorm_cov
import Definitions.Def_GreedNorm_IsValidConf
import Definitions.Def_GreedNorm_IsTBoundedConf

namespace GreedNorm

/-- **Pruning a valid configuration set to a disjoint one.**
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), §3.2, p.8 (PDF 10): "Since the load functions loadi are monotone, given a valid
configuration set A in which some element is contained in several configurations, we can easily
prune the configurations to obtain a valid configuration set A′ so that each element is contained
in at most one configuration and load(A′) ≤ load(A)."

For monotone loads and a valid `A` there are subsets `π(i,S) ⊆ S`, pairwise disjoint over
`A`, such that `A' = {(i, π(i,S)) : (i,S) ∈ A}` is valid, covers the same elements, has
`load_i(π(i,S)) ≤ load_i(S)` for each `(i,S) ∈ A`, and is `t`-bounded for every threshold vector
`t` for which `A` is.

**Formalization Note** "Each element is contained in at most one configuration" is the pairwise
disjointness of the pruned sets. The `t`-bounded clause holds for every `ε` and every
`t : ℕ → ℝ`. -/
theorem prune_configuration_set {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}
    (load : Fin m → Finset U → ℝ) (hmono : ∀ i, SubsamplingSM.Offline.IsMonotoneSetFn (load i))
    (A : Finset (Fin m × Finset U)) (hA : IsValidConf A) :
    ∃ π : Fin m × Finset U → Finset U,
      (∀ c ∈ A, π c ⊆ c.2) ∧
      (∀ c ∈ A, ∀ c' ∈ A, c ≠ c' → Disjoint (π c) (π c')) ∧
      cov (A.image (fun c => (c.1, π c))) = cov A ∧
      IsValidConf (A.image (fun c => (c.1, π c))) ∧
      (∀ c ∈ A, load c.1 (π c) ≤ load c.1 c.2) ∧
      ∀ (ε : ℝ) (t : ℕ → ℝ), IsTBoundedConf ε load t A →
        IsTBoundedConf ε load t (A.image (fun c => (c.1, π c))) := by sorry

end GreedNorm
