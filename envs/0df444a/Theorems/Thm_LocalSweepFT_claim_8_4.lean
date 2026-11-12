-- Prove2me | Theorems.Thm_LocalSweepFT_claim_8_4
-- name    : LocalSweepFT.claim_8_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:38:38.95674+00:00
-- url     : https://prove2.me/theorems/a816549d-054d-48f1-9109-4154178e15c1
-- title:
--   Claim 8.4 — a tree with many leaves per edge has a small subtree with many original leaves
-- statement:
--   Let $\gamma,\beta>0$ and $n\ge1$. For every finite tree $T$ with $\tau\ge\beta n$ edges and $m$ leaves such that $\tau\le\gamma m$, there is a subtree $T'$ (a connected subgraph of $T$) with
--   $$\tau'<\frac{\beta}{2}\,n\ \text{edges},\qquad m'\ge\frac{\beta}{4\gamma}\,n\ \text{original leaves of }T\text{ contained in }T'.$$
--
--   It localizes a large explanation tree to a piece of diameter below $n/2$, whose faults project injectively to the torus.
--
--   Differences from the source:
--   - reading: "a number of leaves m′ ≥ β/(4γ) n. The counted leaves of T′ can be chosen among the original leaves of T" → m′ = the number of original leaves of T (degree one in T) contained in T′; reason: the proof counts "the original leaves of T that it contains" (p.63)
--   - encoding: subtree → connected subgraph of T; reason: §8.2: "a subtree means a connected subgraph of a tree"
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Claim 8.4, p.64 (restated p.57)

import Mathlib

namespace LocalSweepFT

/-- Claim 8.4, p.64 (Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…)). Let `γ, β > 0` and `n` a positive integer. For every
tree `T` with `τ ≥ βn` edges and `m` leaves such that `τ ≤ γm`, there is a subtree `T′` of `T` with
`τ′ < (β/2) n` edges and `m′ ≥ (β/(4γ)) n` leaves, the counted leaves being original leaves of `T`.

**Formalization Note.** A subtree is a connected subgraph of `T` (§8.2). `m′` counts the original
leaves of `T` (vertices of degree one in `T`) that `T′` contains ("we may count the original leaves
of `T` that it contains", p.63). The tree is finite. -/
theorem claim_8_4 (γ β : ℝ) (hγ : 0 < γ) (hβ : 0 < β) (n : ℕ) (hn : 1 ≤ n) {V : Type}
    [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree)
    (hτ : β * n ≤ T.edgeFinset.card)
    (hτm : (T.edgeFinset.card : ℝ) ≤ γ * (Finset.univ.filter (fun v => T.degree v = 1)).card) :
    ∃ T' : T.Subgraph, T'.Connected ∧ (T'.edgeSet.ncard : ℝ) < β / 2 * n ∧
      β / (4 * γ) * n ≤ ({v | v ∈ T'.verts ∧ T.degree v = 1} : Set V).ncard := by sorry

end LocalSweepFT
