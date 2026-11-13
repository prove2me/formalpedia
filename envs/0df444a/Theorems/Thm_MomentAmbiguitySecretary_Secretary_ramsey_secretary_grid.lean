-- Prove2me | Theorems.Thm_MomentAmbiguitySecretary_Secretary_ramsey_secretary_grid
-- name    : MomentAmbiguitySecretary.Secretary.ramsey_secretary_grid
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T11:55:23.188953+00:00
-- url     : https://prove2.me/theorems/890b15ae-7b9e-41fd-bf21-bba0a43e4ec1
-- title:
--   Lemma 6.1 — full randomized cardinal-policy grid bound
-- statement:
--   Fix integers $k\ge m\ge1$ and $\varepsilon>0$. There is $N_0=N_0(m,k,\varepsilon)\ge k$ such that for every $N\ge N_0$, every strictly increasing nonnegative grid $v_0<\cdots<v_{N-1}$ and every measurable randomized cardinal-value secretary policy $\pi$ of horizon $m$, a subset $H$ of exactly $k$ indices satisfies
--
--   $$\Pr_\pi(\text{selects a maximum})\le s_m+\varepsilon+\binom m2/k,$$
--
--   when all labeled values are independent uniform draws from $\{v_h:h\in H\}$ and arrivals are independent uniform random order. Labels and cardinal values are observed, repeated draws are allowed, and any fixed auxiliary information is absorbed into the policy.
--
--   The uniform threshold is chosen before the grid and policy; the subset may depend on them.
--
--   Differences from the source:
--   - encoding: an arbitrary randomized cardinal policy and an ordered grid v_0<...<v_{N-1} → a causal probability kernel at fixed auxiliary information and a strictly increasing Fin N grid; reason: the kernel represents arbitrary private randomization and zero-based indexing names the same finite ordered grid
--   - encoding: grid values in the secretary model, whose values are nonnegative by §2.2 (p.5) though the lemma's sentence does not repeat it → grid values typed Fin N → ℝ≥0; reason: the policy of §2.2 only ever observes nonnegative values, so every grid the model admits is an instance
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied preprint, Lemma 6.1, PDF/printed p.15, SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Values

open MeasureTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal

namespace MomentAmbiguitySecretary.Secretary

/-- Lemma 6.1, pinned preprint PDF/printed pp.15–16.
A fixed auxiliary disclosure is absorbed into the arbitrary cardinal policy. -/
theorem ramsey_secretary_grid (m k : ℕ) (hm : 1 ≤ m) (hk : m ≤ k)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, k ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ v : Fin N → ℝ≥0, StrictMono v → ∀ π : CardinalPolicy m,
      ∃ H : Finset (Fin N), H.card = k ∧
        success π () (fun _ : Fin m => gridDistribution v H) ≤
          classicalValue m + ε + (Nat.choose m 2 : ℝ) / (k : ℝ) := by sorry

end MomentAmbiguitySecretary.Secretary
