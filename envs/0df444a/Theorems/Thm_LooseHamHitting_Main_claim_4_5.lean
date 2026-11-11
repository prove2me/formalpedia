-- Prove2me | Theorems.Thm_LooseHamHitting_Main_claim_4_5
-- name    : LooseHamHitting.Main.claim_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:18:57.035034+00:00
-- url     : https://prove2.me/theorems/2c7602de-df12-48c7-a1dd-dd9b7c39177a
-- title:
--   Claim 4.5 — whp 1 ≤ |B| ≤ n^{1/12}, ∆₁(H_{τ1}) ≤ C log n, ∆₂(H_{τ1}) ≤ 2, and no Berge path of length ≤ 2 joins two vertices of B
-- statement:
--   There is an absolute constant $C>0$ such that, as $n\to\infty$ through even integers, with probability $1-o(1)$ the following hold simultaneously in the random 3-uniform hypergraph process on $[n]$ (with $B$ the set of vertices of degree at most $\lfloor0.01\log n\rfloor$ in $H_{\tau_1}$):
--
--   (i) $1\le|B|\le n^{1/12}$; (ii) $\Delta_1(H_{\tau_1})\le C\log n$; (iii) $\Delta_2(H_{\tau_1})\le2$; (iv) no two vertices of $B$ are joined by a Berge path of length at most two in $H_{\tau_1}$.
--
--   These properties make the triples selected at the vertices of $B$ disjoint and the core near-critical.
--
--   Differences from the source:
--   - encoding: with probability 1 − o(1) (n even, n → ∞) → the probability of (i)–(iv) at n = 2k tends to 1 as k → ∞; reason: explicit limit through even n
--   - encoding: two vertices of B joined by a Berge path of length at most two → distinct u, v ∈ B and a Berge path of length h ∈ {1, 2} from u to v; reason: a path joining two distinct vertices has length ≥ 1
-- source:
--   León, Liu, Hitting time for loose Hamilton cycles in the random hypergraph process, arXiv:2610.29894v1, p. 15, Claim 4.5

import Mathlib
import Definitions.Def_LooseHamHitting_Main_Hypergraph
import Definitions.Def_LooseHamHitting_Main_Process

set_option autoImplicit false

open Classical Filter Topology

namespace LooseHamHitting.Main

/-- Claim 4.5: an absolute constant `C` such that, as `n → ∞` through even integers, with
probability `1 − o(1)`: `1 ≤ |B| ≤ n^{1/12}`, `Δ₁(H_{τ₁}) ≤ C log n`, `Δ₂(H_{τ₁}) ≤ 2`, and no
two distinct vertices of `B` are joined by a Berge path of length at most two in `H_{τ₁}`. -/
theorem claim_4_5 :
    ∃ C : ℝ, 0 < C ∧
      Tendsto (fun k : ℕ => probOrd (2 * k) (fun σ =>
        (1 ≤ (lowSet σ).card ∧ ((lowSet σ).card : ℝ) ≤ ((2 * k : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) ∧
        (maxDegree Finset.univ (hitGraph σ) : ℝ) ≤ C * Real.log ((2 * k : ℕ) : ℝ) ∧
        maxCodegree Finset.univ (hitGraph σ) ≤ 2 ∧
        ∀ u ∈ lowSet σ, ∀ v ∈ lowSet σ, u ≠ v → ∀ h : ℕ, 1 ≤ h → h ≤ 2 →
          ∀ (p : Fin (h + 1) → Fin (2 * k)) (e : Fin h → Finset (Fin (2 * k))),
            IsBergePath (hitGraph σ) h p e → ¬ (p 0 = u ∧ p (Fin.last h) = v)))
        atTop (𝓝 1) := by sorry

end LooseHamHitting.Main
