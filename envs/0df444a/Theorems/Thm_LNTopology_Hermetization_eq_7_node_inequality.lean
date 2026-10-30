-- Prove2me | Theorems.Thm_LNTopology_Hermetization_eq_7_node_inequality
-- name    : LNTopology.Hermetization.eq_7_node_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:29:52.867561+00:00
-- url     : https://prove2.me/theorems/01f4db7d-e4a1-49d0-970c-1491b9af588f
-- title:
--   Inequality (7) at a node: $c(\sum_j\lambda_{i,j})<\frac12\sum_j c(\lambda_{i,j})$ (corrected: (SA+), (SA))
-- statement:
--   Let $\Lambda$ be a Lightning Network, let $c$ and $g_+$ satisfy the cost axioms (MO), (SY), (CI), (SA), (SA+), let $U$ be a node set and $i$ a node with at least one channel into $U$. Write $d_U(i)$, $s_U(i)$, $S_U(i)$ for the degree and the smallest and largest absolute channel flow of $i$ in the sub-network induced on $U$. If
--
--   $$2\,c(S_U(i))\le g_+(d_U(i))\,c(s_U(i)),$$
--
--   then inequality (7) holds at $i$:
--
--   $$c\Bigl(\sum_{j\in U}\lambda_{i,j}\Bigr)<\frac12\sum_{j\in U}c(\lambda_{i,j}).$$
--
--   That is, the new channel from $i$ to the hub costs less than the half of $i$'s channels inside $U$ that $i$ is charged for. Summed over $U$, these inequalities give Lemma B.1.
--
--   Differences from the source:
--   - correction: (SA+) c(kx) < k/g₊(k) c(x) for k ∈ ℝ₊ and every x → (SA+) for natural k ≥ 1 and x > 0; reason: at x = 0 the printed axiom reads 0 < 0 by (CI), so the printed axioms are unsatisfiable; x > 0 is the minimal fix, and asking it only for natural k ≥ 1 (the only values the proof uses, k = d(i)) is a weaker hypothesis
--   - correction: (SA) c(x + y) < c(x) + c(y) for x > y ≥ 0 → (SA) for x > y > 0; reason: at y = 0 the printed axiom reads c(x) < c(x) + c(0) = c(x), unsatisfiable; y > 0 is the minimal fix, and (SA) is not used by the proof
--   - reading: d(i), s(i), S(i), δ(U), disc(U) → computed in the sub-network induced on U (degIn, sIn, SIn, discIn); reason: the proof of Lemma B.1 treats U as the whole network; the reading with degrees in G is false (two linked nodes with many outside channels)
--   - generalization: for every i (a node of U, which the proof treats as the whole network) → any node i with at least one channel into U, in U or not; reason: the inequality only involves i's flows into U; nodes of U are a special case
--   - generalization: g₊(d(i)) > 2c(S(i))/c(s(i)), equivalently d(i) > g₊⁻¹(2c(S(i))/c(s(i))) → 0 < d(i) and 2c(S(i)) ≤ g₊(d(i)) c(s(i)); reason: the printed condition implies this one (c(s(i)) > 0, and g₊⁻¹ takes values in ℝ₊); the non-strict form suffices because the (SA+) step is strict
--   - generalization: c : ℝ → ℝ₊, and g₊ : ℝ₊ → ℝ₊ strictly increasing → c, g : ℝ → ℝ, g strictly increasing on [0, ∞), no sign condition on g; reason: a weaker hypothesis: every pair (c, g₊) of the paper, with g₊ extended arbitrarily off ℝ₊, satisfies CostAxioms; c ≥ 0 follows from (MO), (SY), (CI), and (SA+) forces g(k) > 0 at every natural k ≥ 1
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), proof of Lemma B.1, display (7) and the paragraph after it, p. 11 (PDF p. 12)

import Mathlib
import Definitions.Def_LNTopology_Hermetization_IsLN
import Definitions.Def_LNTopology_Hermetization_CostAxioms
import Definitions.Def_LNTopology_Hermetization_degIn
import Definitions.Def_LNTopology_Hermetization_sIn
import Definitions.Def_LNTopology_Hermetization_SIn__3548ff

namespace LNTopology.Hermetization

/-- **Inequality (7) at one node.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), proof of Lemma B.1, display (7) and the paragraph after it, p. 11: "for every i,
1/2 Σ_{j=1}^n c(λi,j) > c(Σ_{j=1}^n λi,j). (7)" … "it follows that (7) holds if
1/2 d(i)c(s(i)) > d(i)/g₊(d(i)) c(S(i)) ⟺ g₊(d(i)) > 2c(S(i))/c(s(i))".

Let `lam` be an LN, `c, g` satisfy (MO)–(SA+), `U` a node set and `i` a node with at least one
channel into `U`. If `2 c(S_U(i)) ≤ g₊(d_U(i)) c(s_U(i))`, then
`c(Σ_{j∈U} λ_{i,j}) < ½ Σ_{j∈U} c(λ_{i,j})`.

**Formalization Note.** Reading R2: `d(i)`, `s(i)`, `S(i)` are taken in the sub-network induced
on `U` (`degIn`, `sIn`, `SIn`). Generalization G1: the condition `g₊(d(i)) > 2c(S(i))/c(s(i))`
is relaxed to `g₊(d(i)) c(s(i)) ≥ 2c(S(i))` (cleared of the division by `c(s(i)) > 0`, and
non-strict, which suffices because (SA+) is strict). Correction C1: (SA+) as in `CostAxioms`. -/
theorem eq_7_node_inequality {V : Type*} (c g : ℝ → ℝ) (lam : V → V → ℝ) (hLN : IsLN lam)
    (hc : CostAxioms c g) (U : Finset V) (i : V) (hdeg : 0 < degIn lam U i)
    (hcond : 2 * c (SIn lam U i) ≤ g (degIn lam U i) * c (sIn lam U i)) :
    c (∑ j ∈ U, lam i j) < (1 / 2) * ∑ j ∈ U, c (lam i j) := by sorry

end LNTopology.Hermetization
