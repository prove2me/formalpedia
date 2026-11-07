-- Prove2me | Theorems.Thm_MinSumClust_lemma_16
-- name    : MinSumClust.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:51:05.846211+00:00
-- url     : https://prove2.me/theorems/9aa5ff35-1289-4b72-8034-6daafade0cbc
-- title:
--   Lemma 16 — dual payments: a complete run of Algorithm 3 yields a partition into $\gamma_{IC}$-editable clusters (running-time clause carried by Theorem 2)
-- statement:
--   Assume $\gamma_{DC}\ge 2\gamma_{IC}$, $\gamma_{IC}\ge 20$ and $r_S\ge 6$, together with the standing assumptions of §4 ($d$ a metric, $f>0$, $\gamma_{DC},\gamma_{IC},r_S>1$). For every complete run of Algorithm 3, with final dual solution $\alpha^*$, there are quadruples $\langle C^t_{\mathrm{core}},C^t_{\mathrm{del}},C^t_{\mathrm{ins}},C^t_{\mathrm{out}}\rangle$, $t=1,\dots,m$, each $\gamma_{IC}$-editable with respect to $\alpha^*$ and $f$, such that
--
--   $$\bigsqcup_{t}\ (C^t_{\mathrm{core}}\setminus C^t_{\mathrm{del}})\ \sqcup\ C^t_{\mathrm{ins}}\ \sqcup\ C^t_{\mathrm{out}}\ =\ D,$$
--
--   that is, the $3m$ sets are pairwise disjoint and cover all clients. With Lemma 7 this shows $f|\mathcal S_{\mathrm{final}}|+\mathrm{cost}(\mathcal S_{\mathrm{final}})\le\sum_i\alpha^*_i$, the dual payment half of Theorem 2.
--
--   Differences from the source:
--
--   - reading: given the output of Algorithm 3, there is a polynomial-time algorithm that partitions the clients into γ_IC-editable clusters → for every complete run there exists such a partition; reason: the partition is the output of Algorithm 4; its polynomial running time is carried by Theorem 2's polynomial-time clause
--   - reading: Algorithm 3 with choices left open (enumeration order of (s, c), which maximizer, which client a cleaning round removes, order of simultaneous events) → every run of the run relation Alg3Step (all such choices); reason: the paper leaves these choices open; the statement holds for each of them
--   - encoding: a set 𝒞 of quadruples → an indexed family of m quadruples, disjointness of the 3m pieces by position; reason: same partitions
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Lemma 16, p.25 (PDF p.27); restated p.30 (PDF p.32)

import Mathlib
import Definitions.Def_MinSumClust_IsEditable
import Definitions.Def_MinSumClust_Alg3State
import Definitions.Def_MinSumClust_Alg3Step

namespace MinSumClust

/-- **Lemma 16 (dual payments)**, p.25 (PDF p.27); restated p.30 (PDF p.32).

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Lemma 16, p.25.

Assume `γ_DC ≥ 2γ_IC`, `γ_IC ≥ 20` and `r_S ≥ 6`. For every complete run of Algorithm 3, with final
dual solution `α*`, the clients are partitioned into `γ_IC`-editable clusters
`⟨C_core^t, C_del^t, C_ins^t, C_out^t⟩`, `t < m`:
`⊔_t (C_core^t \ C_del^t) ⊔ C_ins^t ⊔ C_out^t = D` (all `3m` pieces pairwise disjoint).

**Formalization Note.** "There is a polynomial-time algorithm that partitions" is read as the
existence of the partition (Algorithm 4 computes it; its running time is carried by Theorem 2). The
statement holds for every run of Algorithm 3 (`Alg3Complete`), whatever choices the run makes. -/
theorem lemma_16 {n : ℕ} (P : Alg3Params n) (hP : P.Valid) (h1 : 2 * P.γIC ≤ P.γDC)
    (h2 : 20 ≤ P.γIC) (h3 : 6 ≤ P.rS) (σ : Alg3State n) (hσ : Alg3Complete P σ) :
    ∃ (m : ℕ) (core del ins out : Fin m → Finset (Fin n)),
      (∀ t, IsEditable P.d σ.α P.f P.γIC (core t) (del t) (ins t) (out t)) ∧
      (∀ s t, s ≠ t → Disjoint (core s \ del s) (core t \ del t)) ∧
      (∀ s t, s ≠ t → Disjoint (ins s) (ins t)) ∧
      (∀ s t, s ≠ t → Disjoint (out s) (out t)) ∧
      (∀ s t, Disjoint (core s \ del s) (ins t)) ∧
      (∀ s t, Disjoint (core s \ del s) (out t)) ∧
      (∀ s t, Disjoint (ins s) (out t)) ∧
      ∀ i : Fin n, ∃ t, i ∈ core t \ del t ∨ i ∈ ins t ∨ i ∈ out t := by sorry

end MinSumClust
