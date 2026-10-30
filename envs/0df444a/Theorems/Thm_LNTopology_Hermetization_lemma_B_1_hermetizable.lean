-- Prove2me | Theorems.Thm_LNTopology_Hermetization_lemma_B_1_hermetizable
-- name    : LNTopology.Hermetization.lemma_B_1_hermetizable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:30:56.582529+00:00
-- url     : https://prove2.me/theorems/cae7d416-742e-44e5-a562-08ce065cd09c
-- title:
--   Lemma B.1: $U$ is hermetizable if $d(i)>g_+^{-1}(2c(S(i))/c(s(i)))$ on $U$ (corrected: $U\neq\emptyset$, (SA+), (SA))
-- statement:
--   Let $\Lambda$ be a Lightning Network on a finite node set $V$ and let $c$ and $g_+$ satisfy the cost axioms (MO), (SY), (CI), (SA), (SA+). Let $U\subseteq V$ be nonempty, and write $d_U(i)$, $s_U(i)$, $S_U(i)$ for the degree and the smallest and largest absolute channel flow of $i$ in the sub-network induced on $U$. If every $i\in U$ satisfies
--
--   $$d_U(i)>0\qquad\text{and}\qquad 2\,c(S_U(i))\le g_+(d_U(i))\,c(s_U(i)),$$
--
--   then $U$ is hermetizable: hermetizing $U$ strictly reduces the cost of the network.
--
--   In the paper's notation the condition is $d(i)>g_+^{-1}\bigl(2c(S(i))/c(s(i))\bigr)$ for all $i\in U$. The lemma says that a set of nodes whose every member has many channels, of comparable sizes, inside the set saves cost by routing all of them through one new hub.
--
--   Differences from the source:
--   - correction: (SA+) c(kx) < k/g₊(k) c(x) for k ∈ ℝ₊ and every x → (SA+) for natural k ≥ 1 and x > 0; reason: at x = 0 the printed axiom reads 0 < 0 by (CI), so the printed axioms are unsatisfiable; x > 0 is the minimal fix, and asking it only for natural k ≥ 1 (the only values the proof uses, k = d(i)) is a weaker hypothesis
--   - correction: U is any subset of V → U is nonempty; reason: for U = ∅ the condition holds vacuously but hermetizing ∅ only adds an isolated node, so the cost does not drop
--   - correction: (SA) c(x + y) < c(x) + c(y) for x > y ≥ 0 → (SA) for x > y > 0; reason: at y = 0 the printed axiom reads c(x) < c(x) + c(0) = c(x), unsatisfiable; y > 0 is the minimal fix, and (SA) is not used by the proof
--   - reading: hermetizing U reduces its cost → the total cost strictly drops: c(G′_U) < c(G); reason: only the channels inside U and at v₀ change, so this is the same as a drop of the cost carried by U (cost identity milestone)
--   - reading: d(i), s(i), S(i), δ(U), disc(U) → computed in the sub-network induced on U (degIn, sIn, SIn, discIn); reason: the proof of Lemma B.1 treats U as the whole network; the reading with degrees in G is false (two linked nodes with many outside channels)
--   - generalization: d(i) > g₊⁻¹(2c(S(i))/c(s(i))) for all i ∈ U → 0 < d(i) and 2c(S(i)) ≤ g₊(d(i)) c(s(i)) for all i ∈ U; reason: the printed condition implies this one (c(s(i)) > 0, g₊ strictly increasing, g₊⁻¹ ≥ 0); the non-strict form suffices because the (SA+) step is strict
--   - generalization: c : ℝ → ℝ₊, and g₊ : ℝ₊ → ℝ₊ strictly increasing → c, g : ℝ → ℝ, g strictly increasing on [0, ∞), no sign condition on g; reason: a weaker hypothesis: every pair (c, g₊) of the paper, with g₊ extended arbitrarily off ℝ₊, satisfies CostAxioms; c ≥ 0 follows from (MO), (SY), (CI), and (SA+) forces g(k) > 0 at every natural k ≥ 1
--   - encoding: c(G) = Σ_{i>j} c(λ_{i,j}); the new node v₀; λ′_{0,l} = Σ_i λ_{i,l} → c(G) = ½ Σ_{i,j} c(λ_{i,j}); Option V with none = v₀; λ′_{v₀,l} = −Σ_{w∈U} λ_{l,w}; reason: Lean convention; the same numbers on an LN (antisymmetry and (SY), (CI)), and λ′ stays antisymmetric
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Lemma B.1, p. 11 (PDF p. 12)

import Mathlib
import Definitions.Def_LNTopology_Hermetization_IsLN
import Definitions.Def_LNTopology_Hermetization_CostAxioms
import Definitions.Def_LNTopology_Hermetization_degIn
import Definitions.Def_LNTopology_Hermetization_sIn
import Definitions.Def_LNTopology_Hermetization_SIn__3548ff
import Definitions.Def_LNTopology_Hermetization_Hermetizable

namespace LNTopology.Hermetization

/-- **Lemma B.1 (a node-wise sufficient condition for hermetizability).**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Lemma B.1, p. 11: "Let G = (V, E) be a LN, and let U ⊆ V be a subset of vertices. U is
hermetizable if d(i) > g₊⁻¹(2c(S(i))/c(s(i))) for all i ∈ U."

Let `lam` be an LN and `c, g` satisfy (MO)–(SA+). A nonempty node set `U` in which every node `i`
has a channel into `U` and satisfies `2 c(S_U(i)) ≤ g₊(d_U(i)) c(s_U(i))` is hermetizable.

**Formalization Note.** Correction C2: `U` is nonempty (hermetizing `∅` adds an isolated node and
does not reduce the cost). Reading R2: `d`, `s`, `S` are taken in the sub-network induced on
`U`. Generalization G1: the printed `d(i) > g₊⁻¹(2c(S(i))/c(s(i)))` implies `d(i) > 0` and
`g₊(d(i)) c(s(i)) > 2c(S(i))`; the non-strict form is assumed. Reading R1: hermetizable means the
total cost strictly drops. Correction C1: (SA+) as in `CostAxioms`. -/
theorem lemma_B_1_hermetizable {V : Type*} [Fintype V] [DecidableEq V] (c g : ℝ → ℝ)
    (lam : V → V → ℝ) (hLN : IsLN lam) (hc : CostAxioms c g) (U : Finset V)
    (hU : U.Nonempty)
    (hcond : ∀ i ∈ U, 0 < degIn lam U i ∧
      2 * c (SIn lam U i) ≤ g (degIn lam U i) * c (sIn lam U i)) :
    Hermetizable c lam U := by sorry

end LNTopology.Hermetization
