-- Prove2me | Theorems.Thm_KawasakiSOS_Threshold_opening_lemma
-- name    : KawasakiSOS.Threshold.opening_lemma
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:04:17.325171+00:00
-- url     : https://prove2.me/theorems/c9be33da-16f3-478a-a21c-57a5444d8112
-- title:
--   Lemma 4.10: the opening
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $6\le k\le n$, let $B=\{b_0,\dots,b_4\}$ be a block of five consecutive sites, let $t\in\{b_1,b_2,b_3\}$, and let $h\in\Omega$. Write $h^{B,t}$ for the configuration that agrees with $h$ off $B$, vanishes on $B\setminus\{t\}$, and has $h(B)$ units at $t$. Then there is a sequence of at most $Cn$ teleports from $h$ to $h^{B,t}$ such that every teleport endpoint $g$ satisfies $M(g)\le M(h)$ and differs from $h$ only on $B\cup\{r,o\}$. Here $r$ is the smallest column at which $h$ is maximal, and $o\in\{b_0-1,b_4+1\}$.
--
--   The opening clears a block of five sites without raising the energy, and the closing is the same construction reversed.
--
--   Differences from the source:
--   - reading: "O(n) teleports" → one constant C > 0, quantified before every parameter; reason: the O(·) of the source is read as an absolute constant, uniform in the displayed parameters
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Lemma 4.10, p. 13 (PDF p. 14)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_IsOpening

namespace KawasakiSOS.Threshold

/-- Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Lemma 4.10, p. 13 (PDF p. 14).

Formalization Notes:
- reading: "O(n) teleports" → one constant C > 0, quantified before every parameter. The O(·) of the source is read as an absolute constant, uniform in the displayed parameters. -/
theorem opening_lemma : ∃ C : ℝ, 0 < C ∧ ∀ (n k : ℕ) [NeZero k], 6 ≤ k → k ≤ n → ∀ (h : Config n k) (b t : ZMod k), (t = b + 1 ∨ t = b + 2 ∨ t = b + 3) →
    ∃ (o : ZMod k) (g : Config n k) (ops : List (ZMod k × ZMod k)) (l : List (Config n k)),
      IsOpening h b t o g ops l ∧ (ops.length : ℝ) ≤ C * (n : ℝ) := by sorry

end KawasakiSOS.Threshold
