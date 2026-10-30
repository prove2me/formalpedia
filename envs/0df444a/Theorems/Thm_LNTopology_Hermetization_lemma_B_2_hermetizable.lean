-- Prove2me | Theorems.Thm_LNTopology_Hermetization_lemma_B_2_hermetizable
-- name    : LNTopology.Hermetization.lemma_B_2_hermetizable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:31:33.714235+00:00
-- url     : https://prove2.me/theorems/54b4bef9-936f-4ce6-95e8-d31faad1914b
-- title:
--   Lemma B.2: $U$ is hermetizable if $\delta(U)\ge g_+^{-1}(2\,\mathrm{disc}(U))$ (corrected: (SA+), (SA))
-- statement:
--   Let $\Lambda$ be a Lightning Network on a finite node set $V$ and let $c$ and $g_+$ satisfy the cost axioms (MO), (SY), (CI), (SA), (SA+). Let $U\subseteq V$ be a nonempty node set in which every node has a channel to another node of $U$, and write $\delta(U)=\min_{v\in U}d_U(v)$ and $\mathrm{disc}(U)=\max_{v\in U}c(S_U(v))/c(s_U(v))$ for the minimum degree and the discrepancy of the sub-network induced on $U$. If there is $t\ge0$ with
--
--   $$g_+(t)\ge 2\,\mathrm{disc}(U)\qquad\text{and}\qquad d_U(v)\ge t\ \text{ for every } v\in U,$$
--
--   then $U$ is hermetizable. With $t=g_+^{-1}(2\,\mathrm{disc}(U))$ this is the paper's condition $\delta(U)\ge g_+^{-1}(2\,\mathrm{disc}(U))$.
--
--   The lemma turns the node-wise condition of Lemma B.1 into a single condition on the minimum degree, which is what Theorem 3.8 obtains from the average degree.
--
--   Differences from the source:
--   - correction: (SA+) c(kx) < k/g₊(k) c(x) for k ∈ ℝ₊ and every x → (SA+) for natural k ≥ 1 and x > 0; reason: at x = 0 the printed axiom reads 0 < 0 by (CI), so the printed axioms are unsatisfiable; x > 0 is the minimal fix, and asking it only for natural k ≥ 1 (the only values the proof uses, k = d(i)) is a weaker hypothesis
--   - correction: (SA) c(x + y) < c(x) + c(y) for x > y ≥ 0 → (SA) for x > y > 0; reason: at y = 0 the printed axiom reads c(x) < c(x) + c(0) = c(x), unsatisfiable; y > 0 is the minimal fix, and (SA) is not used by the proof
--   - reading: hermetizing U reduces its cost → the total cost strictly drops: c(G′_U) < c(G); reason: only the channels inside U and at v₀ change, so this is the same as a drop of the cost carried by U (cost identity milestone)
--   - reading: d(i), s(i), S(i), δ(U), disc(U) → computed in the sub-network induced on U (degIn, sIn, SIn, discIn); reason: the proof of Lemma B.1 treats U as the whole network; the reading with degrees in G is false (two linked nodes with many outside channels)
--   - reading: δ(U) and disc(U) → hypotheses U nonempty and every node of U has a channel into U; reason: s(v) is undefined for a node without a channel, so δ(U) and disc(U) are defined only then
--   - generalization: δ(U) ≥ g₊⁻¹(2disc(U)) → some t ≥ 0 has g₊(t) ≥ 2disc(U) and d_U(v) ≥ t for all v ∈ U; reason: the printed case is t = g₊⁻¹(2disc(U)), and the hypothesis needs no inverse of g₊
--   - generalization: c : ℝ → ℝ₊, and g₊ : ℝ₊ → ℝ₊ strictly increasing → c, g : ℝ → ℝ, g strictly increasing on [0, ∞), no sign condition on g; reason: a weaker hypothesis: every pair (c, g₊) of the paper, with g₊ extended arbitrarily off ℝ₊, satisfies CostAxioms; c ≥ 0 follows from (MO), (SY), (CI), and (SA+) forces g(k) > 0 at every natural k ≥ 1
--   - encoding: c(G) = Σ_{i>j} c(λ_{i,j}); the new node v₀; λ′_{0,l} = Σ_i λ_{i,l} → c(G) = ½ Σ_{i,j} c(λ_{i,j}); Option V with none = v₀; λ′_{v₀,l} = −Σ_{w∈U} λ_{l,w}; reason: Lean convention; the same numbers on an LN (antisymmetry and (SY), (CI)), and λ′ stays antisymmetric
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Lemma B.2, p. 12 (PDF p. 13)

import Mathlib
import Definitions.Def_LNTopology_Hermetization_IsLN
import Definitions.Def_LNTopology_Hermetization_CostAxioms
import Definitions.Def_LNTopology_Hermetization_degIn
import Definitions.Def_LNTopology_Hermetization_discIn
import Definitions.Def_LNTopology_Hermetization_Hermetizable

namespace LNTopology.Hermetization

/-- **Lemma B.2 (minimum degree against discrepancy).**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Lemma B.2, p. 12: "A set U is hermetizable if δ(U) ≥ g₊⁻¹(2disc(U))."

Let `lam` be an LN and `c, g` satisfy (MO)–(SA+). Let `U` be a nonempty node set in which every
node has a channel into `U`. If some `t ≥ 0` has `g₊(t) ≥ 2 disc(U)` and every node of `U` has
at least `t` channels into `U`, then `U` is hermetizable.

**Formalization Note.** Readings R2, R3: `δ(U)` and `disc(U)` are the minimum degree and the
discrepancy of the sub-network induced on `U`; they are defined only when `U` is nonempty and
every node of `U` has a channel into `U` (otherwise `s(v)` is undefined), which are hypotheses.
Generalization G1: `g₊⁻¹(2disc(U))` is replaced by any `t ≥ 0` with `g₊(t) ≥ 2disc(U)`; the
printed case is `t = g₊⁻¹(2disc(U))`. Reading R1 and correction C1 as in Lemma B.1. -/
theorem lemma_B_2_hermetizable {V : Type*} [Fintype V] [DecidableEq V] (c g : ℝ → ℝ)
    (lam : V → V → ℝ) (hLN : IsLN lam) (hc : CostAxioms c g) (U : Finset V)
    (hU : U.Nonempty) (hdeg : ∀ v ∈ U, 0 < degIn lam U v)
    (ht : ∃ t : ℝ, 0 ≤ t ∧ 2 * discIn c lam U ≤ g t ∧ ∀ v ∈ U, t ≤ (degIn lam U v : ℝ)) :
    Hermetizable c lam U := by sorry

end LNTopology.Hermetization
