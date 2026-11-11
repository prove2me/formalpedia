-- Prove2me | Theorems.Thm_LooseHamHitting_Main_theorem_1_1
-- name    : LooseHamHitting.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:18:51.964504+00:00
-- url     : https://prove2.me/theorems/f009beeb-fc06-4c1a-a629-fab529206145
-- title:
--   Theorem 1.1 — in the random 3-uniform hypergraph process, P[τ_LHC = τ₁] → 1 as n → ∞ through even integers
-- statement:
--   Let $(H_t)_{t=0}^{\binom n3}$ be the random 3-uniform hypergraph process on $[n]=\{1,\dots,n\}$: $H_0=\emptyset$ and, for $0\le t<\binom n3$, conditional on $H_t$, a triple chosen uniformly from $\binom{[n]}3\setminus H_t$ is added to obtain $H_{t+1}$. Let
--   $$\tau_1=\min\{t:\delta_1(H_t)\ge1\},\qquad\tau_{LHC}=\min\{t:H_t\text{ contains a loose Hamilton cycle}\}.$$
--   Then
--   $$\lim_{\substack{n\to\infty\\ n\text{ even}}}P[\tau_{LHC}=\tau_1]=1.$$
--
--   A loose Hamilton cycle has no isolated vertex, so $\tau_{LHC}\ge\tau_1$ always; the theorem says that with high probability the obvious obstruction is the only one, the 3-uniform analogue of Kahn's hitting-time theorem for perfect matchings.
--
--   Differences from the source:
--   - encoding: the process adding a uniformly chosen missing triple at each step → a uniformly random ordering of all \binom{n}{3} triples, H_t its first t triples; reason: same law of (H_t)
--   - encoding: τ_LHC possibly undefined; the event τ_LHC = τ₁ → τ₁, τ_LHC in WithTop ℕ (⊤ = undefined); the event requires both finite and equal; reason: an undefined τ_LHC makes the event false
--   - encoding: n → ∞ through even integers → the limit along n = 2k, k → ∞; reason: same filter
-- source:
--   León, Liu, Hitting time for loose Hamilton cycles in the random hypergraph process, arXiv:2610.29894v1, p. 1, Theorem 1.1

import Mathlib
import Definitions.Def_LooseHamHitting_Main_Hypergraph
import Definitions.Def_LooseHamHitting_Main_Process

set_option autoImplicit false

open Classical Filter Topology

namespace LooseHamHitting.Main

/-- Theorem 1.1: in the random 3-uniform hypergraph process on `[n]`, as `n → ∞` through even
integers, `P[τ_LHC = τ₁] → 1`. -/
theorem theorem_1_1 :
    Tendsto (fun k : ℕ => probOrd (2 * k) (fun σ => HittingTimesEqual σ)) atTop (𝓝 1) := by sorry

end LooseHamHitting.Main
