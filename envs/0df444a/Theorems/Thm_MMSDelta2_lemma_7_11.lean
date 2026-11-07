-- Prove2me | Theorems.Thm_MMSDelta2_lemma_7_11
-- name    : MMSDelta2.lemma_7_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:01:49.783077+00:00
-- url     : https://prove2.me/theorems/11def5c3-c5f2-4d9f-a257-c4e4891d889b
-- title:
--   Lemma 7.11 — allocations giving everyone $\tau$ split the core by rows
-- statement:
--   In the constructed five-agent instance, let $(A_z)_z$ be an allocation in which every agent receives value at least $\tau$. Then the KPW core goods are allocated by rows, up to relabeling: there is a permutation $\pi$ of $\{1,\dots,5\}$ such that
--
--   $$A_z\cap M_{core}=R_{\pi(z)}\qquad\text{for every agent }z.$$
--
--   This rules out the column partition of the core in MMS allocations.
--
--   **Formalization Note** Agents are numbered $0=p$, $1=a^*$, $2,3=q_1,q_2$, $4=f$; $\mathrm{MMS}_z$ is computed for the real-valued copy of the constructed instance.
--
--   Differences from the source:
--   - encoding: agents p, a*, q₁, q₂, f; MMS of the constructed instance → agents 0–4 of buildInstance; MMS_z = CutChoose.mu of its real copy; reason: fixed numbering; the values are integers
--   - encoding: allocated by rows, up to relabeling → ∃ permutation π with A z ∩ M_core = R_{π z} for all z; reason: same statement
--   - generalization: the §7 standing assumption: (W, T) is a LexMax4Partition-Promise instance, promised to admit a solution (p.27) → no promise: the statement holds for every 4-PARTITION instance I; reason: the proof (p.35) uses only Proposition 5.3, (7.2) and Observation 7.6, never a solution; promise instances are a special case
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), Lemma 7.11, p.35 (PDF p.37)

import Mathlib
import Definitions.Def_MMSDelta2_buildInstance
import Definitions.Def_MMSDelta2_HasMMSAllocation

namespace MMSDelta2

/-- **Lemma 7.11**, p.35 (PDF p.37).

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…).

In any allocation in which every agent receives value at least `τ`, the KPW core goods are
allocated by rows, up to relabeling.

**Formalization Note.** Agents are `0 = p` (puzzle-solving), `1 = a*` (lex-opt indicator), `2, 3 = q_1, q_2`
(row-forcing), `4 = f` (anchor); rows are 0-based (`rowGoods 4` is `R_5`). Values are the real
copies `realVal I.buildInstance` of the integer values; `MMS_z` is `StrategicAlloc.CutChoose.mu`.
An allocation is a family of pairwise disjoint bundles covering all goods; "allocated by rows, up
to relabeling" is a permutation `π` with `A_z ∩ M_core = R_{π z}` for every agent `z`. No promise
is used. -/
theorem lemma_7_11 (I : FourPartInstance) (A : Fin 5 → Finset (Fin (numCore + 4 * I.q * I.q)))
    (hA : StrategicAlloc.RRFair.IsAllocation A)
    (hτ : ∀ z, (I.tau : ℝ) ≤ StrategicAlloc.RRFair.val (realVal I.buildInstance) z (A z)) :
    ∃ π : Equiv.Perm (Fin 5), ∀ z, A z ∩ I.coreGoods = I.rowGoods (π z) := by sorry

end MMSDelta2
