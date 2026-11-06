-- Prove2me | Theorems.Thm_MethodFulfillment_alaei_threshold
-- name    : MethodFulfillment.alaei_threshold
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:10:50.824486+00:00
-- url     : https://prove2.me/theorems/083186fc-eae6-4cec-ae3d-47d7d6f94943
-- title:
--   Appendix D, p.59 — Alaei (2014): for $\gamma\le1-1/\sqrt{S+3}$ the threshold stays below $S$
-- statement:
--   Let $n\ge1$ and $0\le\gamma\le1-1/\sqrt{n+3}$, and let $\mu^1,\mu^2,\dots\in[0,1]$. Let $F^t$ be the magician's recursion of Appendix D with inputs $\mu$ and level $\gamma$. Then for every $t$ with $\sum_{s<t}\mu^s\le n$
--   $$F^t(n-1)\ge\gamma ,$$
--   equivalently the threshold $\theta^t=\min\{l:F^t(l)\ge\gamma\}$ is at most $n-1$. So a magician holding $n$ units never makes its inventory available once all $n$ units are used: it never requires more than $n$ units.
--
--   The paper takes this from Alaei (2014, Theorem 4), which it cites without proof; it is the only place where the constant $1-1/\sqrt{S+3}$ enters.
--
--   **Formalization Note** A statement about the deterministic recursion, with no probability space. The Lean recursion at $t$ is the paper's $F^{t+1}$, and the hypothesis is on the inputs used to compute it.
--
--   Differences from the source:
--   - reading: "whenever γik ≤ 1 − 1/√(Sik + 3), magician (i,k) never requires more than Sik inventory" (citing Alaei 2014, Theorem 4) → for every γ ∈ [0, 1 − 1/√(n+3)] and μ ∈ [0,1]^ℕ with prefix sums ≤ n, the recursion satisfies F^t(n − 1) ≥ γ (threshold ≤ n − 1); reason: the cited theorem is about Alaei's boxes and wands; this is its content for the threshold rule of Appendix D, which never makes inventory available above the threshold
--   - encoding: F_{W^t}, μ^t with t ≥ 1 → magF μ γ t, μ t with t ≥ 0 (Lean t is the paper's t + 1); reason: Lean convention; the same recursion
--   - generalization: Definition 4: the magician starts with S_ik > 0 units (with S_ik < T) → S_ik < T not assumed; reason: the recursion needs no such condition; the case S_ik < T is included
--   - encoding: the magician's inventory Sik > 0 (Definition 4) → n : ℕ with 1 ≤ n; reason: inventory is counted in units (p.15, "one unit"); Sik > 0 is 1 ≤ n
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), Appendix D, p.59; p.17; citing Alaei (2014), Theorem 4

import Mathlib
import Definitions.Def_MethodFulfillment_magF

namespace MethodFulfillment

/-- **Alaei's bound for the magician recursion** (Amil, Makhdoumi & Wei, manuscript, PDF sha256
197c13b9…, Appendix D, p.59, and p.17, citing Alaei (2014), Theorem 4: "whenever
γik ≤ 1 − 1/√(Sik + 3), magician (i,k) never requires more than Sik inventory"): for every
`n ≥ 1`, every `γ` with `0 ≤ γ ≤ 1 − 1/√(n + 3)`, every sequence of consumption probabilities
`μ_t ∈ [0, 1]` and every `t` with `∑_{s < t} μ_s ≤ n`, the recursion of Appendix D satisfies
`F_{W^{t+1}}(n − 1) ≥ γ`; equivalently the threshold `θ^{t+1}` is at most `n − 1`, so the
magician never makes its inventory available once `n` units are used.

**Formalization Note.** A statement about the deterministic recursion `magF` (0-based: `magF μ γ t`
is the paper's `F_{W^{t+1}}`); it involves no probability space. `0 ≤ γ` is Definition 4's
`γik ∈ [0,1]`. -/
theorem alaei_threshold (n : ℕ) (hn : 1 ≤ n) (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hγ : γ ≤ 1 - 1 / Real.sqrt ((n : ℝ) + 3)) (μ : ℕ → ℝ) (hμ : ∀ t, 0 ≤ μ t ∧ μ t ≤ 1)
    (t : ℕ) (ht : ∑ s ∈ Finset.range t, μ s ≤ (n : ℝ)) :
    γ ≤ magF μ γ t (n - 1) := by sorry

end MethodFulfillment
