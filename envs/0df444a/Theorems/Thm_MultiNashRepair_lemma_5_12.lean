-- Prove2me | Theorems.Thm_MultiNashRepair_lemma_5_12
-- name    : MultiNashRepair.lemma_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:35:12.614195+00:00
-- url     : https://prove2.me/theorems/9da5f978-62aa-4ad1-8efd-4b37a260aafc
-- title:
--   Lemma 5.12 — the joint reachable-state invariant (I1)–(I4) and $\mu>5d$
-- statement:
--   Fix admissible controls for $\sigma$ and $m\ge m_0$. At the beginning of every iteration reached by Algorithm 1, simultaneously:
--   1. (I1) the profile is a product profile, rational when the payoffs are rational, every stored mass is a nonnegative rational, every stored generation is legal (intensity $t$, activation law with $\gamma^{(s)}_i<3/m$), and $h_i=\sum_sA^{(s)}t^{(s)}\gamma^{(s)}_i$, $H=\sum_ih_i$ (5.52);
--   2. (I2) $h_i\ge0$, $0\le H\le L_0$, $v_i=mh_i-H\le R_0H$ (5.53);
--   3. (I3) every stored generation satisfies $\sum_{i\ne j}\gamma^{(s)}_id^{(s)}_{ij}(y_j)\le L_{\mathrm{col}}/m$ with $L_{\mathrm{col}}=9$, for every $j$ and mixed $y_j$ (5.54);
--   4. (I4) the certificate events of Lemma 5.2 exist.
--
--   Every nonterminal iteration has $\mu>5d$. A failed LP executes a legal repair (for every optimal dual and every choice of best responses) that adds one new generation. Once $H>0$, every subsequent state has $H>0$.
--
--   Differences from the source:
--   - reading: (I4) disjoint augmented certificate events with the laws of Lemma 5.2 → `CertLaw`; reason: Lemma 5.2 in measure form; the proofs use only the dominations
--   - generalization: (I1) as printed → also $t^{(s)}=t$ and $\gamma^{(s)}_i<3/m$ for every stored generation; reason: Lemma 5.5 gives these at creation and the proof of Lemma 5.6 uses them ((5.31) at each stored generation); the item contains (I1)
--   - generalization: the algorithm's optimal dual and best responses → every optimal dual and every pure best responses; reason: contains the algorithm's choices
--   - encoding: once $H^{(k)}>0$, all later iterates have positive memory → one step: $H>0$ and a step to $s'$ give $H'>0$; reason: iterating along a run gives the statement; every successor is again reachable
--   - encoding: the preservation clauses for both branches → the invariants at every reachable state; reason: a successor of a reachable state is reachable at $k+1$
--   - generalization: rational payoffs → real payoffs in $[0,1]$, with the rationality of the profile in (I1) asserted for rational payoffs; reason: the other clauses use only $0\le u_i\le1$; the correction deficits (3.9) are payoff expressions (p.42), so (I1)'s rational profile needs rational payoffs; on the paper's games the item is (I1)–(I4) verbatim
-- source:
--   J. Tang, S. Ding, C. Fang, Breaking the One-Player Extension Barrier: History-Aware Repair for Multiplayer Approximate Nash Equilibria, arXiv:2611.06076 (preprint; held version, sha256 34b911ed…5c14), Lemma 5.12, (5.52)–(5.54), pp.39–40; proof pp.40–43

import Mathlib
import Definitions.Def_NashAmplification_Filtering_Model
import Definitions.Def_MultiNashRepair_IDRH

open NashAmplification.Filtering (Mixed Utility Tuple BoundedGame)
open Finset

namespace MultiNashRepair

/-- **Lemma 5.12 (Joint Reachable-State Invariant)** (Tang, Ding, Fang, arXiv:2611.06076,
Lemma 5.12, (5.52)–(5.54), pp.39–40).

At the beginning of every iteration reached by Algorithm 1 with `m ≥ m0`, simultaneously:
- (I1) the profile is a rational product profile, every stored mass `A^{(s,k)}` is a nonnegative
  rational, every stored generation is legal (created with intensity `t` and an activation law
  with `γ^{(s)}_i < 3/m`), and the memory is exactly `h_i = Σ_s A^{(s,k)} t^{(s)} γ^{(s)}_i`,
  `H = Σ_i h_i` (5.52);
- (I2) `h_i ≥ 0`, `0 ≤ H ≤ L0`, `v_i = m h_i − H ≤ R0 H` (5.53);
- (I3) every stored generation satisfies the original-column inequality with `Lcol = 9` (5.54);
- (I4) the certificate events of Lemma 5.2 exist (here: `CertLaw`).
Every nonterminal iteration has `µ > 5d`. A failed LP executes a legal repair (every optimal dual,
every choice of best responses) adding one new generation. Once `H > 0`, every following state
has positive memory.

**Formalization Note.** The game is any real game with payoffs in `[0,1]`; the rationality of
the profile in (I1) is asserted for rational payoffs, the paper's setting (§2, p.5), since the
correction deficits (3.9) are payoff expressions (p.42). (I4) is Lemma 5.2 in measure form
(`CertLaw`). "Legal" for stored
generations includes `t^{(s)} = t` and `γ^{(s)}_i < 3/m`, which Lemma 5.5 gives at creation and
which the proof of Lemma 5.6 uses for stored generations ((5.31), p.31). The preservation
clauses of the lemma are the invariants at `k + 1` (every successor of a reachable state is
reachable); positivity of memory is stated for one step, which gives it along every run. -/
theorem lemma_5_12 {σ : ℚ} (ctrl : Controls σ) {m : ℕ} {n : Fin m → ℕ} (hm : ctrl.m0 ≤ m)
    (hn : ∀ i, 0 < n i) (u : Utility n) (hu : BoundedGame u) {kk : ℕ} {s : State n}
    (hs : Reach ctrl u kk s) :
    let k := ctrl.knobs
    (AGT.IsMixedProfile s.x ∧ ((∀ i a, IsRat (u i a)) → ∀ i a, IsRat (s.x i a)) ∧
      (∀ g ∈ s.gens, GenLegal g ∧ IsRat g.A ∧ g.t = k.t ∧ ∀ i, g.γ i < 3 / m) ∧
      (∀ i, s.h i = (s.gens.map fun g => g.A * g.t * g.γ i).sum) ∧ s.H = ∑ i, s.h i) ∧
    ((∀ i, 0 ≤ s.h i) ∧ 0 ≤ s.H ∧ s.H ≤ k.L0 ∧ ∀ i, (m : ℝ) * s.h i - s.H ≤ k.R0 * s.H) ∧
    ColumnBound u s.gens 9 ∧
    CertLaw s.x s.gens ∧
    (¬ Terminal σ u s → 5 * (ctrl.d : ℝ) < ctrl.mu (scaled u s.x) s.H) ∧
    (∀ (w : (i : Fin m) → Fin (n i) → ℝ) (α : ℝ) (arev acor : (i : Fin m) → Fin (n i)),
      ¬ Terminal σ u s → ¬ Passes ctrl u s → DualOptimal u s.x ctrl.η w α →
      IsRevBR u (rY k s w) (rDelta k s w) arev →
      IsFwdBR u (rXt k s w arev) (rE k u s w arev) acor →
      RepairLegal k u s w arev ∧
        (repairState k u s w arev acor).gens.length = s.gens.length + 1) ∧
    (∀ s' : State n, Step ctrl u s s' → 0 < s.H → 0 < s'.H) := by sorry

end MultiNashRepair
