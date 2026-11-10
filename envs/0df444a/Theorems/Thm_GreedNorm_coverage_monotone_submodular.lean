-- Prove2me | Theorems.Thm_GreedNorm_coverage_monotone_submodular
-- name    : GreedNorm.coverage_monotone_submodular
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:44:33.848814+00:00
-- url     : https://prove2.me/theorems/b6d5eb57-fea8-4086-ad0b-28485946289d
-- title:
--   §3.2 — coverage $h(\mathcal A)=|\mathrm{cov}(\mathcal A)|$ is monotone submodular with marginal $|S\setminus\mathrm{cov}(\mathcal A)|$
-- statement:
--   Let $V=[m]\times 2^U$ be the set of configurations and $h(\mathcal A)=|\mathrm{cov}(\mathcal A)|$ for $\mathcal A\subseteq V$. Then $h(\emptyset)=0$, $h$ is monotone and submodular,
--
--   $$
--   h(\mathcal A\cup\mathcal B)+h(\mathcal A\cap\mathcal B)\le h(\mathcal A)+h(\mathcal B),
--   $$
--
--   and the marginal of adding a configuration is
--
--   $$
--   h(\mathcal A\cup\{(i,S)\})-h(\mathcal A)=|S\setminus\mathrm{cov}(\mathcal A)| .
--   $$
--
--   Coverage is the objective of the configuration reformulation (ThreshBudgCovConfig) to which Theorem 3.10 is applied.
--
--   Differences from the source:
--   - generalization: h on configuration sets, i.e. collections of at most m configurations; marginal of adding (i, S) to A → h on all finite sets of configurations; the marginal identity for every configuration (it reads 0 = 0 when (i, S) ∈ A); reason: the source's sets are among these, so the statement specializes to the source's
--   - encoding: configurations (i, S), i ∈ [m], S ⊆ U; configuration sets → Fin m × Finset U (types 0-based); Finset of configurations; reason: Lean convention; same instances
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), §3.2 Expressing ThreshBudgAlloc in terms of configurations, p.7 (PDF 9)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn
import Definitions.Def_GreedNorm_cov

namespace GreedNorm

/-- **Coverage over configurations is monotone submodular, with marginal `|S \ cov(A)|`.**
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), §3.2 "Expressing ThreshBudgAlloc in terms of configurations", p.7 (PDF 9): "Let h be the
monotone submodular function over configurations where h(A) = |cov(A)|. Observe that the marginal
of h when adding (i, S) to A is hA((i, S)) = |S \ cov(A)|."

The function `h(A) = |cov(A)|` on sets of configurations `(i, S) ∈ [m] × 2^U` has `h(∅) = 0`,
is monotone and submodular, and `h(A ∪ {(i,S)}) − h(A) = |S \ cov(A)|`.

**Formalization Note** `h` is defined on all finite sets of configurations, not only on those
with at most `m` members, and the marginal identity holds for every configuration (it reads
`0 = 0` when `(i,S) ∈ A`). Submodularity is the public `NonmonotoneSubmod.Shared.Submodular`. -/
theorem coverage_monotone_submodular {U : Type} [Fintype U] [DecidableEq U] (m : ℕ) :
    ((cov (∅ : Finset (Fin m × Finset U))).card : ℝ) = 0 ∧
      SubsamplingSM.Offline.IsMonotoneSetFn (fun A : Finset (Fin m × Finset U) => ((cov A).card : ℝ)) ∧
      NonmonotoneSubmod.Shared.Submodular
        (fun A : Finset (Fin m × Finset U) => ((cov A).card : ℝ)) ∧
      ∀ (A : Finset (Fin m × Finset U)) (c : Fin m × Finset U),
        ((cov (insert c A)).card : ℝ) - ((cov A).card : ℝ) = ((c.2 \ cov A).card : ℝ) := by sorry

end GreedNorm
