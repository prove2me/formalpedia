-- Prove2me | Theorems.Thm_OneTwoThree_Weighting_lemma_5_parity_feasibility
-- name    : OneTwoThree.Weighting.lemma_5_parity_feasibility
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-11T20:09:12.182763+00:00
-- url     : https://prove2.me/theorems/5b797317-cbd1-4bfa-908c-cf18f4b50dcd
-- title:
--   Lemma 5 parity feasibility — the odd-parity vertex set V_o has even cardinality
-- statement:
--   The parity-feasibility computation opening the proof of Lemma 5
--   (Keusch, *A Solution to the 1-2-3 Conjecture*, arXiv:2303.02611v4, p. 6).
--
--   The proof's first stage builds a parity subgraph (T-join) on the vertex set
--   $V_o := R' \cup \{v \in B : \alpha(v) \ne 2\deg(v)\}$ — the vertices required
--   to end with odd weighted degree — and the leaf-induction construction needs
--   $|V_o|$ to be even. Since $\alpha(v) \in \{2\deg(v)-1, 2\deg(v), 2\deg(v)+1\}$
--   for $v \in B$, we have $\alpha(v)$ odd iff $\alpha(v) \ne 2\deg(v)$; hence
--   $|\{v \in B : \alpha(v) \ne 2\deg(v)\}| = |\{v \in B : \alpha(v)$
--   odd$\}| \equiv \sum_{v\in B}\alpha(v) \pmod 2$. With $R' \subseteq B^c$
--   disjoint from $B$, $|R' \cup \{v \in B : \alpha(v) \ne 2\deg(v)\}| =
--   |R'| + |\{v \in B : \alpha(v) \ne 2\deg(v)\}|$ is even by the hypothesis
--   $|R'| + \sum_{v\in B}\alpha(v)$ even ($hpar$ of Lemma 5).
--
--   The degree is abstracted to a plain function $d : V \to \mathbb N$
--   (instantiate $d := G.\mathrm{degree}$ for the mission use); no graph structure
--   and no flow machinery is involved — the s-t network belongs to Lemma 4
--   (used by Lemma 3), not to any Lemma-5 child. On PUBLISHED this unblocks the
--   PROVE of the parity subgraph (T-join) child and hence of Lemma 5 itself.
--
--   Parent `OneTwoThree.Weighting.lemma_5` (`18cd221d-d23a-4ae5-97c8-ca2db074a231`)
--   live-verified Open with `deprecated_at=null` immediately before posting.
-- source:
--   Keusch, A Solution to the 1-2-3 Conjecture, arXiv:2303.02611v4, p. 6, proof of Lemma 5 stage (a) (parity-subgraph premise)

import Mathlib
import Definitions.Def_OneTwoThree_Weighting_Setting

namespace OneTwoThree.Weighting

/-- Parity feasibility for the odd-parity vertex set of Lemma 5's proof
(Keusch, arXiv:2303.02611v4, p. 6, proof of Lemma 5, stage (a)).

The proof's parity subgraph (T-join) step needs `V_o := R' ∪ {v ∈ B : α v ≠ 2·d v}`
— the vertices required to end with odd weighted degree — to have EVEN cardinality.
That parity comes from `hpar`: since `α v ∈ {2·d v − 1, 2·d v, 2·d v + 1}` for
`v ∈ B`, we have `α v` odd `↔` `α v ≠ 2 * d v`, so
`#{v ∈ B : α v ≠ 2 * d v} = #{v ∈ B : Odd (α v)} ≡ ∑_{v ∈ B} α v (mod 2)`;
with `R'` disjoint from `B` (`hR'`), `#(R' ∪ {v ∈ B : …}) = #R' + #{v ∈ B : …}`
is even by `hpar`. Instantiate `d := G.degree` for the mission use. -/
theorem lemma_5_parity_feasibility {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset V) (α : V → ℕ) (d : V → ℕ)
    (hα : ∀ v ∈ B, (α v : ℤ) = 2 * (d v : ℤ) - 1 ∨ (α v : ℤ) = 2 * (d v : ℤ) ∨
      (α v : ℤ) = 2 * (d v : ℤ) + 1)
    (R' : Finset V) (hR' : R' ⊆ Bᶜ)
    (hpar : Even (Finset.card R' + Finset.sum B (fun v => α v))) :
    Even (Finset.card (R' ∪ B.filter (fun v => α v ≠ 2 * d v))) := by sorry

end OneTwoThree.Weighting
