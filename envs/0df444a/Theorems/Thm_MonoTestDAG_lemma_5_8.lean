-- Prove2me | Theorems.Thm_MonoTestDAG_lemma_5_8
-- name    : MonoTestDAG.lemma_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:10:50.504296+00:00
-- url     : https://prove2.me/theorems/6c0419fe-92f1-489d-98f7-8cccf92bf7a9
-- title:
--   Lemma 5.8 — hardness is preserved by a cloud lift
-- statement:
--   Let $U=(L,R;E)$ be an $(s,\eta)$-PMRS graph with $|L|=|R|=n_0$ and $|E|=\Theta(n_0s)$, with an $(s,\eta)$-PMRS witness having $(q_0,1/20)$-bounded matching exposure. Let $\tilde G:=\mathrm{Cl}_D(U)$ for some $1\le D\le s$. Then:
--
--   1. $\tilde G$ is transitively reduced;
--   2. with $n_{\mathrm{cl}}:=|V(\tilde G)|$, $m_{\mathrm{cl}}:=|E(\mathrm{TR}(\tilde G))|$ and $\ell_{\mathrm{cl}}:=|E(\mathrm{TC}(\tilde G))|$,
--   $$
--   n_{\mathrm{cl}}=2n_0(D+1),\quad m_{\mathrm{cl}}=|E|+2n_0D=\Theta(n_0s),\quad \ell_{\mathrm{cl}}=|E|(D+1)^2+2n_0D=\Theta(n_0sD^2);
--   $$
--   3. if $n_0$ is sufficiently large, then for $\varepsilon_\star:=\eta/8$ there are distributions $\tilde D^\pm$ over functions on $\tilde G$ such that $\tilde D^+$ is supported on monotone functions, a function drawn from $\tilde D^-$ is $\varepsilon_\star$-far with probability at least $9/10$, and every $\tilde Q\subseteq V(\tilde G)$ with $|\tilde Q|\le q_0$ has $\mathrm{TV}(\mathrm{Tr}(\tilde D^+,\tilde Q),\mathrm{Tr}(\tilde D^-,\tilde Q))\le1/20$. Consequently, every randomized non-adaptive $\varepsilon_\star$-tester on $\tilde G$, even with two-sided error, makes more than $q_0$ queries.
--
--   The lift increases $\ell$ relative to $n$ while preserving hardness, which produces the $\ell$-dependent lower bound.
--
--   Differences from the source:
--   - encoding: |E| = Θ(n₀s) and the Θ of (ii) → for every C with |E| ≤ C n₀ s: η n₀ s ≤ m_cl ≤ (C+2) n₀ s and η n₀ s D² ≤ ℓ_cl ≤ (4C+2) n₀ s D²; reason: the hypothesis is used only there, and |E| ≥ Σ|M_i| ≥ η n₀ s gives the lower bound
--   - reading: "n₀ sufficiently large" → n₀ ≥ N with N depending on η only; reason: the proof's Chernoff bound uses only η and n₀
--   - reading: s ∈ ℕ in Definition 4.3 → s ≥ 1, inside `IsPMRSWitness`; reason: [K] is defined only for positive K (p.1); s = 0 makes Lemma 5.2 false on an edgeless graph
--   - reading: distributions over functions → `PMF` on functions; reason: for a non-discrete D the average acceptance probability needs joint measurability the paper never states; every distribution the paper constructs is finitely supported
--   - encoding: randomized non-adaptive tester → the structure `Tester`: arbitrary probability space in `Type`, query set a function of the seed, decision a function of the seed and the answers on that set, acceptance event of each input measurable in the seed; reason: the paper's definition in §2.4; a universe-0 probability space loses no tester of the paper; measurability only makes the acceptance probability defined
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), Lemma 5.8, p.32

import Mathlib
import Definitions.Def_MonoTestDAG_Tester
import Definitions.Def_MonoTestDAG_IsPMRSWitness
import Definitions.Def_MonoTestDAG_exposeSet
import Definitions.Def_MonoTestDAG_transcript
import Definitions.Def_MonoTestDAG_cloudEdge
import Definitions.Def_MonoTestDAG_numTC
import Definitions.Def_MonoTestDAG_numTR

namespace MonoTestDAG

/-- **Lemma 5.8 (Hardness is preserved by a cloud lift).** Let `U = (L, R; E)` be an
`(s, η)`-PMRS graph with `|L| = |R| = n₀` and `|E| = Θ(n₀ s)`, with an `(s, η)`-PMRS witness `M`
having `(q₀, 1/20)`-bounded matching exposure, and let `G̃ := Cl_D(U)` with `1 ≤ D ≤ s`. Then
1. `G̃` is transitively reduced;
2. `n_cl = 2n₀(D + 1)`, `m_cl = |E| + 2n₀D = Θ(n₀ s)` and `ℓ_cl = |E|(D + 1)² + 2n₀D = Θ(n₀ s D²)`;
3. if `n₀` is sufficiently large, then for `ε⋆ := η/8` there are distributions `D̃⁺`, `D̃⁻` over
   functions on `G̃` such that `D̃⁺` is supported on monotone functions, `D̃⁻` is `ε⋆`-far with
   probability at least `9/10`, and every `Q̃ ⊆ V(G̃)` with `|Q̃| ≤ q₀` has
   `TV(Tr(D̃⁺, Q̃), Tr(D̃⁻, Q̃)) ≤ 1/20`. Consequently every randomized non-adaptive `ε⋆`-tester on
   `G̃` with two-sided error makes more than `q₀` queries.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), Lemma 5.8, p.32.

**Formalization Note.** The hypothesis `|E| = Θ(n₀ s)` is used only by the `Θ` parts of (ii); they
are stated with explicit constants: if `|E| ≤ C n₀ s` then `η n₀ s ≤ m_cl ≤ (C + 2) n₀ s` and
`η n₀ s D² ≤ ℓ_cl ≤ (4C + 2) n₀ s D²` (the lower bounds come from `|E| ≥ Σ|M_i| ≥ η n₀ s`).
"`n₀` sufficiently large" is a threshold `N` depending on `η` only. -/
theorem lemma_5_8 :
    ∀ η : ℝ, ∃ N : ℕ, ∀ {L R : Type} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
      (EU : Finset (L × R)) (s : ℕ) (M : Fin s → Finset (L × R)) (q₀ D : ℕ),
      IsPMRSWitness EU η s M → HasBoundedExposure M q₀ (1 / 20) → 1 ≤ D → D ≤ s →
      IsTransReduced (cloudEdge EU D) ∧
      Fintype.card (CloudV L R D) = 2 * Fintype.card L * (D + 1) ∧
      numTR (cloudEdge EU D) = EU.card + 2 * Fintype.card L * D ∧
      numTC (cloudEdge EU D) = EU.card * (D + 1) ^ 2 + 2 * Fintype.card L * D ∧
      (∀ C : ℝ, (EU.card : ℝ) ≤ C * (Fintype.card L : ℝ) * (s : ℝ) →
        η * (Fintype.card L : ℝ) * (s : ℝ) ≤ (numTR (cloudEdge EU D) : ℝ) ∧
        (numTR (cloudEdge EU D) : ℝ) ≤ (C + 2) * (Fintype.card L : ℝ) * (s : ℝ) ∧
        η * (Fintype.card L : ℝ) * (s : ℝ) * (D : ℝ) ^ 2 ≤ (numTC (cloudEdge EU D) : ℝ) ∧
        (numTC (cloudEdge EU D) : ℝ) ≤ (4 * C + 2) * (Fintype.card L : ℝ) * (s : ℝ) * (D : ℝ) ^ 2) ∧
      (N ≤ Fintype.card L →
        ∃ Dp Dm : PMF (CloudV L R D → ℝ),
          (∀ f ∈ Dp.support, IsMonotone (cloudEdge EU D) f) ∧
          (9 / 10 : ENNReal) ≤ Dm.toOuterMeasure {f | IsFar (cloudEdge EU D) (η / 8) f} ∧
          (∀ Q : Finset (CloudV L R D), Q.card ≤ q₀ → trTV Dp Dm Q ≤ 1 / 20) ∧
          (∀ (T : Tester (CloudV L R D)) (q : ℝ), IsTwoSidedTester (cloudEdge EU D) (η / 8) T →
            T.QueriesAtMost q → (q₀ : ℝ) < q)) := by sorry

end MonoTestDAG
