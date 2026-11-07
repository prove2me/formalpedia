-- Prove2me | Theorems.Thm_MonoTestDAG_lemma_5_2
-- name    : MonoTestDAG.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:11:14.646248+00:00
-- url     : https://prove2.me/theorems/1a36bc93-dba5-4591-aeab-a7eb63506e8c
-- title:
--   Lemma 5.2 — a lower bound from bounded matching exposure
-- statement:
--   Let $U=(L,R;E)$ be an $(s,\eta)$-PMRS graph with $|L|=|R|=n_0$, and let $M$ be an $(s,\eta)$-PMRS witness with $(q_0,\rho)$-bounded matching exposure, $\rho\le1/20$. Let $G=P(U)$ and $\varepsilon_\star:=\eta/8$. If $n_0$ is sufficiently large, there are distributions $D^+$, $D^-$ over functions on $G$ such that:
--
--   1. every function in the support of $D^+$ is monotone;
--   2. a function drawn from $D^-$ is $\varepsilon_\star$-far with probability at least $9/10$;
--   3. for every query set $Q\subseteq V(G)$ with $|Q|\le q_0$, $\mathrm{TV}(\mathrm{Tr}(D^+,Q),\mathrm{Tr}(D^-,Q))\le\rho$.
--
--   Consequently, every randomized non-adaptive $\varepsilon_\star$-tester on $G$, even with two-sided error, makes more than $q_0$ queries.
--
--   Differences from the source:
--   - reading: "n₀ sufficiently large" → n₀ ≥ N with N depending on η only; reason: the proof's Chernoff bound uses only η and n₀
--   - reading: s ∈ ℕ in Definition 4.3 → s ≥ 1, inside `IsPMRSWitness`; reason: [K] is defined only for positive K (p.1); s = 0 makes Lemma 5.2 false on an edgeless graph
--   - reading: distributions over functions → `PMF` on functions; reason: for a non-discrete D the average acceptance probability needs joint measurability the paper never states; every distribution the paper constructs is finitely supported
--   - encoding: randomized non-adaptive tester → the structure `Tester`: arbitrary probability space in `Type`, query set a function of the seed, decision a function of the seed and the answers on that set, acceptance event of each input measurable in the seed; reason: the paper's definition in §2.4; a universe-0 probability space loses no tester of the paper; measurability only makes the acceptance probability defined
--   - encoding: "makes more than q₀ queries" → every q bounding the queries on every seed has q₀ < q; reason: worst-case query count
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), Lemma 5.2, p.25

import Mathlib
import Definitions.Def_MonoTestDAG_Tester
import Definitions.Def_MonoTestDAG_IsPMRSWitness
import Definitions.Def_MonoTestDAG_exposeSet
import Definitions.Def_MonoTestDAG_transcript

namespace MonoTestDAG

/-- **Lemma 5.2 (A lower bound from bounded matching exposure).** Let `U = (L, R; E)` be an
`(s, η)`-PMRS graph with `|L| = |R| = n₀`, and `M = (M_1, …, M_s)` an `(s, η)`-PMRS witness with
`(q₀, ρ)`-bounded matching exposure, `ρ ≤ 1/20`. Let `G = P(U)` and `ε⋆ := η/8`. If `n₀` is
sufficiently large, there are distributions `D⁺`, `D⁻` over functions on `G` such that
1. every function in the support of `D⁺` is monotone;
2. a function drawn from `D⁻` is `ε⋆`-far from monotonicity with probability at least `9/10`;
3. for every query set `Q ⊆ V(G)` with `|Q| ≤ q₀`, `TV(Tr(D⁺, Q), Tr(D⁻, Q)) ≤ ρ`.
Consequently, every randomized non-adaptive `ε⋆`-tester for monotonicity on `G` with two-sided
error makes more than `q₀` queries.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), Lemma 5.2, p.25.

**Formalization Note.** "`n₀` sufficiently large" is a threshold `N` depending on `η` only.
"Makes more than `q₀` queries" is: whenever every run makes at most `q` queries, `q > q₀`. -/
theorem lemma_5_2 :
    ∀ η : ℝ, ∃ N : ℕ, ∀ {L R : Type} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
      (EU : Finset (L × R)) (s : ℕ) (M : Fin s → Finset (L × R)) (q₀ : ℕ) (ρ : ℝ),
      IsPMRSWitness EU η s M → HasBoundedExposure M q₀ ρ → ρ ≤ 1 / 20 →
      N ≤ Fintype.card L →
      ∃ Dp Dm : PMF (L ⊕ R → ℝ),
        (∀ f ∈ Dp.support, IsMonotone (bipDAG EU) f) ∧
        (9 / 10 : ENNReal) ≤ Dm.toOuterMeasure {f | IsFar (bipDAG EU) (η / 8) f} ∧
        (∀ Q : Finset (L ⊕ R), Q.card ≤ q₀ → trTV Dp Dm Q ≤ ρ) ∧
        (∀ (T : Tester (L ⊕ R)) (q : ℝ), IsTwoSidedTester (bipDAG EU) (η / 8) T →
          T.QueriesAtMost q → (q₀ : ℝ) < q) := by sorry

end MonoTestDAG
