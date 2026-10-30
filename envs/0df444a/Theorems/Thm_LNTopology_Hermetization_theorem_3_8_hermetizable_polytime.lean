-- Prove2me | Theorems.Thm_LNTopology_Hermetization_theorem_3_8_hermetizable_polytime
-- name    : LNTopology.Hermetization.theorem_3_8_hermetizable_polytime
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:32:51.247798+00:00
-- url     : https://prove2.me/theorems/c7e9bada-bec3-42c1-8bdb-89fe004f4924
-- title:
--   Theorem 3.8: $\bar d(G)>2g_+^{-1}(2\,\mathrm{disc}(G))$ implies hermetizable, found in polynomial time (corrected: (SA+), (SA))
-- statement:
--   Assume a cost function $c$ and a function $g_+$ satisfying the cost axioms (MO), (SY), (CI), (SA), (SA+). There are constants $C$ and $k$ such that, for every number of nodes $n$ and every flow matrix $\Lambda$ on $n$ nodes:
--
--   1. the algorithm of Theorem 3.8 (compute $\mathrm{disc}(G)$, then peel the vertices of degree $\le g_+^{-1}(2\,\mathrm{disc}(G))$) makes at most $C(n+1)^k$ ticks of the real-RAM model, on every input;
--   2. if $\Lambda$ is a Lightning Network and there is $t\ge0$ with
--   $$g_+(t)\ge 2\,\mathrm{disc}(G)\qquad\text{and}\qquad \bar d(G)>2t,$$
--   then the network is hermetizable, and the node set returned by the algorithm is hermetizable: hermetizing it strictly reduces the cost.
--
--   With $t=g_+^{-1}(2\,\mathrm{disc}(G))$ the hypothesis is the paper's $\bar d(G)>2g_+^{-1}(2\,\mathrm{disc}(G))$. Here $\bar d(G)$ is the average number of channels per node and $\mathrm{disc}(G)$ the largest ratio $c(S(v))/c(s(v))$ between the costs of a node's largest and smallest channel. The theorem says that a dense Lightning Network with channels of comparable sizes always admits a cost-reducing hub, and that such a hub can be placed efficiently.
--
--   **Formalization Note** "Polynomial time" is counted in ticks of the mission's real-RAM model: each read of a flow, each query of $c$ or $g_+$, each real comparison or operation and each loop iteration costs one tick. The constants $C,k$ are chosen before the input and the bound holds on every input. The algorithm is an explicit program, not an existence statement.
--
--   Differences from the source:
--   - correction: (SA+) c(kx) < k/g₊(k) c(x) for k ∈ ℝ₊ and every x → (SA+) for natural k ≥ 1 and x > 0; reason: at x = 0 the printed axiom reads 0 < 0 by (CI), so the printed axioms are unsatisfiable; x > 0 is the minimal fix, and asking it only for natural k ≥ 1 (the only values the proof uses, k = d(i)) is a weaker hypothesis
--   - correction: (SA) c(x + y) < c(x) + c(y) for x > y ≥ 0 → (SA) for x > y > 0; reason: at y = 0 the printed axiom reads c(x) < c(x) + c(0) = c(x), unsatisfiable; y > 0 is the minimal fix, and (SA) is not used by the proof
--   - reading: hermetizing U reduces its cost → the total cost strictly drops: c(G′_U) < c(G); reason: only the channels inside U and at v₀ change, so this is the same as a drop of the cost carried by U (cost identity milestone)
--   - reading: there is a polynomial-time algorithm → the explicit algorithm findHermetizable makes at most C(n+1)^k ticks on every input, with C, k chosen before the input, in the real-RAM model with unit-cost oracles for c and g₊; reason: the inputs are real numbers and real functions with no bit encoding; the algorithm is the paper's (disc, then Lemma B.3's peeling)
--   - generalization: d̄(G) > 2g₊⁻¹(2disc(G)) → some t ≥ 0 has g₊(t) ≥ 2disc(G) and d̄(G) > 2t; reason: the printed case is t = g₊⁻¹(2disc(G)), and the hypothesis needs no inverse of g₊
--   - generalization: disc(G) = max over all nodes v → maximum over the nodes with at least one channel (0 if none); reason: equal to the printed value whenever every node has a channel, which the printed disc presupposes
--   - generalization: c : ℝ → ℝ₊, and g₊ : ℝ₊ → ℝ₊ strictly increasing → c, g : ℝ → ℝ, g strictly increasing on [0, ∞), no sign condition on g; reason: a weaker hypothesis: every pair (c, g₊) of the paper, with g₊ extended arbitrarily off ℝ₊, satisfies CostAxioms; c ≥ 0 follows from (MO), (SY), (CI), and (SA+) forces g(k) > 0 at every natural k ≥ 1
--   - encoding: nodes V = {1, …, n}, the new node v₀, c(G) = Σ_{i>j} c(λ_{i,j}), λ′_{0,l} = Σ_i λ_{i,l} → Fin n, Option (Fin n) with none = v₀, c(G) = ½ Σ_{i,j} c(λ_{i,j}), λ′_{v₀,l} = −Σ_{w∈U} λ_{l,w}; reason: Lean convention; the same instances (the two cost expressions and the two forms of λ′ agree on an LN)
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Theorem 3.8, p. 8 (PDF p. 9); proof on p. 12 (PDF p. 13)

import Mathlib
import Definitions.Def_LNTopology_Hermetization_IsLN
import Definitions.Def_LNTopology_Hermetization_CostAxioms
import Definitions.Def_LNTopology_Hermetization_avgDeg
import Definitions.Def_LNTopology_Hermetization_disc
import Definitions.Def_LNTopology_Hermetization_Hermetizable
import Definitions.Def_LNTopology_Hermetization_LNHermetizable
import Definitions.Def_LNTopology_Hermetization_findHermetizable

namespace LNTopology.Hermetization

/-- **Theorem 3.8 (dense Lightning Networks are hermetizable, and a polynomial-time algorithm
finds a hermetizable set).**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Theorem 3.8, p. 8: "Assume a cost function with the properties (MO)-(SA+). If G is a LN
with d̄(G) > 2g₊⁻¹(2disc(G)) then it is hermetizible and there is a polynomial-time algorithm to
find a set U whose hermetization reduces its cost."

There are constants `C, k` such that for every `n`, every flow matrix `lam` on `Fin n` and all
`c, g`: the algorithm `findHermetizable` runs in at most `C (n + 1)^k` ticks; and if `lam` is an
LN, `c, g` satisfy (MO)–(SA+) and `d̄(G) > 2t` for some `t ≥ 0` with `g₊(t) ≥ 2disc(G)`, then
the LN is hermetizable and the set returned by `findHermetizable` is hermetizable.

**Formalization Note.**
* Correction C1 (and C4): (SA+) and (SA) as in `CostAxioms`.
* Generalization G1: `d̄(G) > 2g₊⁻¹(2disc(G))` becomes `∃ t ≥ 0, g₊(t) ≥ 2disc(G) ∧ d̄(G) > 2t`;
  the printed case is `t = g₊⁻¹(2disc(G))`.
* Generalization G2: `disc(G)` is the maximum over nodes with a channel (`disc`); it is the
  printed value whenever every node has a channel, which the printed `disc` presupposes.
* Reading R4: "polynomial-time" is counted in ticks of the real-RAM model (`tick`), with
  `C, k` chosen before the input and the bound holding on every input; the algorithm is the
  explicit witness `findHermetizable` (the paper's Lemma B.3 peeling with the threshold
  `g₊⁻¹(2disc(G))`).
* Reading R1: "reduces its cost" is a strict drop of the total cost.
* Encoding E2: nodes are `Fin n`; no lower bound on `n` and no condition on isolated nodes is
  assumed. -/
theorem theorem_3_8_hermetizable_polytime :
    ∃ C k : ℕ, ∀ (n : ℕ) (lam : Fin n → Fin n → ℝ) (c g : ℝ → ℝ),
      ((findHermetizable lam c g).run 0).2 ≤ C * (n + 1) ^ k ∧
      (IsLN lam → CostAxioms c g →
        (∃ t : ℝ, 0 ≤ t ∧ 2 * disc c lam ≤ g t ∧ 2 * t < avgDeg lam) →
        LNHermetizable c lam ∧
          Hermetizable c lam ((findHermetizable lam c g).run 0).1) := by sorry

end LNTopology.Hermetization
