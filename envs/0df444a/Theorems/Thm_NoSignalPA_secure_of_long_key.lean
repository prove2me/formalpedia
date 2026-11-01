-- Prove2me | Theorems.Thm_NoSignalPA_secure_of_long_key
-- name    : NoSignalPA.secure_of_long_key
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:05:59.49+00:00
-- url     : https://prove2.me/theorems/ca35dfc3-abe3-4455-8fd7-76441c715b03
-- title:
--   Main result for long keys: if $N_r+2\le N_s+\sqrt{N_r}$, every $h$ satisfies (5) (corrected: not in the paper; fills the regime its proof omits)
-- statement:
--   Assume $N_r+2\le N_s+\sqrt{N_r}$. Then every function $h:\{0,1\}^{N_r}\to\{0,1\}^{N_s}$ is secure: for every choice of Eve's sets $Z,E$, every $(N_r+2)$-partite nonsignaling box $P$, every input $\mathbf y$ of Bob and every input $z_0$ of Eve,
--
--   $$
--   \sum_{\mathbf k}\ \sup_{z}\ \sum_{e}\Bigl|P_{\mathbf k,e|\mathbf x=\mathbf 0,z}-2^{-N_s}P_{e|z}\Bigr|\ \le\ \sqrt{2^{\,N_s+\sqrt{N_r}}}\ \langle\mathrm{CHSH}|^{\otimes N_r}|P_{\mathbf a,\mathbf b|\mathbf x,\mathbf y}\rangle .
--   $$
--
--   This statement is not in the paper. The paper proves the main result through Lemma 2, whose proof needs $|\beta5^M8^{-N_r}|\le1$; that constraint holds only when $N_s+\sqrt{N_r}\le N_r+2$. This milestone covers the remaining key lengths, so that the main result holds for all $N_r,N_s$ as stated.
--
--   Differences from the source:
--   - correction: the proof of the main result via Lemma 2 for all Nr, Ns ('the chosen value for β satisfies the required constraint', p.5) → a separate statement for Nr + 2 ≤ Ns + √Nr, where every h is secure; reason: the constraint fails for long keys: at Nr = 144, Ns = 160 Lemma 2 is false for every h (see lemma_2), so the paper's proof does not reach these key lengths, while the main result still holds there
--   - reading: (Nr + 2)-partite nonsignaling distribution P_{a,b,e|x,y,z} → IsNonsignaling: for each of Alice's Nr systems, Bob (one system) and Eve, summing out that party's output leaves a quantity independent of that party's input; reason: pp. 1–2 define no signaling as 'the marginals only depend on their corresponding observables', with Bob's systems as one; the single-party conditions imply those for every subset of parties
--   - generalization: Eve's input z and output e, with Σ_e and max_z (no alphabets fixed) → Z and E arbitrary types in a universe u, P x y z a PMF on (a, b, e), max_z as ⨆ and Σ_e as tsum in ℝ≥0∞; reason: every finite alphabet is such a type and then ⨆ is the maximum and tsum the finite sum; the security predicate quantifies over more boxes, so it specializes to the paper's
--   - reading: P_{k,e|x=0,z}, P_{e|z} and P_{a,b|x,y} (inputs of other parties not shown) → key and Eve marginals read at x = 0 and any Bob input y; P_{a,b|x,y} read at any Eve input z₀; IsSecure quantifies over y and z₀; reason: under no signaling these marginals do not depend on the omitted inputs; quantifying over them is the stronger reading
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, Main result, eq. (5), p.2, for the regime excluded by the constraint of eq. (14), p.5 (not stated in the paper)

import Mathlib
import Definitions.Def_NoSignalPA_IsSecure

namespace NoSignalPA

/-- **(Not in the paper.) For `Nr + 2 ≤ Ns + √Nr` every hash function is secure.**
Added for Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, Main result, eq. (5), p. 2 (PDF p. 2). The paper's proof goes through Lemma 2, whose
proof needs `|β 5^M 8^{−Nr}| ≤ 1` (p. 5); "the chosen value for β satisfies the required
constraint" holds only when `Ns + √Nr ≤ Nr + 2`. This milestone covers the remaining key lengths.

If `Nr + 2 ≤ Ns + √Nr`, then every `h : {0,1}^{Nr} → {0,1}^{Ns}` satisfies the bound (5) for every
`(Nr + 2)`-partite nonsignaling box: `IsSecure h`.

**Formalization Note.** Together with `lemma_2` and `secure_of_entrywise` this yields the main
result for all `Nr, Ns`; the two regimes share the boundary `Ns + √Nr = Nr + 2`. -/
theorem secure_of_long_key.{u} {Nr Ns : ℕ} (hN : (Nr : ℝ) + 2 ≤ Ns + Real.sqrt Nr)
    (h : Str Nr → Str Ns) : IsSecure.{u} h := by sorry

end NoSignalPA
