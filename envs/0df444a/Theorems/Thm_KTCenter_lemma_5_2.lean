-- Prove2me | Theorems.Thm_KTCenter_lemma_5_2
-- name    : KTCenter.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:29:10.293104+00:00
-- url     : https://prove2.me/theorems/69d1a7b1-e53f-4d5e-83e9-b79a566a1841
-- title:
--   Lemma 5.2 — allowed keys and variable pairs: $P_v\subseteq I_v$, $|P_v|\le K$, $\beta w_v$-dense, $|E_0|\le4W$
-- statement:
--   Let $(w_v)$ be nonnegative integers, $0<\beta<1$, $m=\lceil1/(2\beta)\rceil$, $K=2m+1$, and $W=\sum_v w_v$. Then:
--
--   1. every $P_v$ is a nonempty subset of $I_v$ with $|P_v|\le K$;
--   2. for every $v$ and every integer $t\in I_v$ there is $a\in P_v$ with $|a-t|\le\beta w_v$;
--   3. $|E_0|\le4W$.
--
--   The finite key sets lose little against integer positions and leave few pairs whose order is undecided.
--
--   Differences from the source:
--
--   - encoding: candidate v and positions as numbers 1, …, d → the 1-based label lab v as a rational; reason: Lean convention; same values
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), Lemma 5.2, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_KTCenter_KeyDomains

namespace KTCenter

/-- **Lemma 5.2** (Allowed keys and variable pairs), p.25 (PDF p.27).

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…).

**Formalization Note.** Algorithm 2's inputs: any nonnegative integers `w_v` and `0 < β < 1`. `E₀`
and `P_v` do not depend on the input rankings. -/
theorem lemma_5_2 {d : ℕ} (w : Fin d → ℕ) (β : ℚ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∀ v, (keySet w β v).Nonempty ∧ (↑(keySet w β v) : Set ℚ) ⊆ keyInterval w v ∧
      (keySet w β v).card ≤ keyBound β) ∧
    (∀ (v : Fin d) (t : ℤ), (t : ℚ) ∈ keyInterval w v →
      ∃ a ∈ keySet w β v, |a - t| ≤ β * (w v : ℚ)) ∧
    (variablePairs w β).card ≤ 4 * totalW w := by sorry

end KTCenter
