-- Prove2me | Theorems.Thm_HLambdaG_Main_Supplement_theorem_3
-- name    : HLambdaG.Main.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:04:00.436032+00:00
-- url     : https://prove2.me/theorems/36ecd25f-ad5d-4616-8cca-4abaf82a1973
-- title:
--   Theorem 3, p. 640 — in the setting of §1.1, (18) implies (15) for T₂(s) = T_[s] + U_[s], and s⁻¹T₂(s) has the limit of n⁻¹T_n
-- statement:
--   Consider the setting of §1.1, with $F(s,t)=\sum_{k=1}^{[s]}F_k(t)$. Let $\{S_k\}$ be a nonnegative finite sequence satisfying (18):
--   $$
--   \frac{S_n}{T_n}\to0\quad\text{and}\quad n^{-1}\sum_{k=1}^{n}\bigl[F_k(\infty)-F_k(T_k+S_k)\bigr]\to0 .
--   $$
--   Let $U_n=\max\{S_k:1\le k\le n\}$ and $T_2(s)=T_{[s]}+U_{[s]}$ as in (19). Then:
--
--   1. condition (15) holds for $T_2$: $\;s^{-1}\bigl[F(s,\infty)-F(s,T_2(s))\bigr]\to0$ as $s\to\infty$;
--   2. for every real $c$, if $n^{-1}T_n\to c$ then $s^{-1}T_2(s)\to c$;
--   3. if $n^{-1}T_n\to\infty$ then $s^{-1}T_2(s)\to\infty$.
--
--   Theorem 3 turns the sequence condition (18) into the general condition (15) with an explicit time change, so that Theorem 1(b) applies in the discrete setting. Parts 2 and 3 express "$\lim_{s\to\infty}s^{-1}T_2(s)=\lim_{n\to\infty}n^{-1}T_n$ whenever the latter limit exists", for finite and infinite limits.
--
--   **Formalization Note** $T_2$ is built as the published `TimeChange`. It is right-continuous because it is constant on each $[n,n+1)$. "Whenever the latter limit exists" is not a hypothesis of the (15) clause: (15) is concluded unconditionally from (18), and the rate clauses are implications.
--
--   Differences from the source:
--
--   - encoding: s, t ∈ [0, ∞), customers k = 1, 2, … → s, t : ℝ≥0; customers indexed by ℕ with a dummy index 0 (F_0 = 0); reason: Lean convention; the index 0 carries no customer and every sum starts at k = 1, so no instance changes
-- source:
--   Glynn and Whitt, Extensions of the queueing relations L = λW and H = λG, Oper. Res. 37 (1989), p. 640, Theorem 3, with (18), (19) on p. 640; https://doi.org/10.1287/opre.37.4.634

import Mathlib
import Definitions.Def_HLambdaG_Main_Supplement_Discrete

open scoped NNReal

namespace HLambdaG.Main.Supplement

open Filter Topology

/-- Theorem 3, p. 640: in the setting of §1.1, (18) implies (15) for the time change
`T₂(s) = T_{[s]} + U_{[s]}` of (19), and `lim s⁻¹T₂(s) = lim n⁻¹T_n` whenever the latter
limit exists (finite or `+∞`). -/
theorem theorem_3 (D : DiscreteSetting) (S : ℕ → ℝ≥0) (h18 : D.Cond18 S) :
    Cond15 D.input (D.T2 S) ∧
      (∀ c : ℝ, Tendsto (fun n : ℕ => (D.T n : ℝ) / (n : ℝ)) atTop (𝓝 c) →
        Tendsto (fun s : ℝ≥0 => ((D.T2 S).T s : ℝ) / (s : ℝ)) atTop (𝓝 c)) ∧
      (Tendsto (fun n : ℕ => (D.T n : ℝ) / (n : ℝ)) atTop atTop →
        Tendsto (fun s : ℝ≥0 => ((D.T2 S).T s : ℝ) / (s : ℝ)) atTop atTop) := by sorry

end HLambdaG.Main.Supplement
