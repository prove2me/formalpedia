-- Prove2me | Theorems.Thm_MultiNashRepair_lemma_5_6
-- name    : MultiNashRepair.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:35:28.580142+00:00
-- url     : https://prove2.me/theorems/950aa355-3182-4775-b0d0-4ee0c67e4012
-- title:
--   Lemma 5.6 — the total frozen deficit is at most $120u/m$, retention $\ge c$, and $\varsigma^+\ge c\varsigma+D-E$
-- statement:
--   Fix admissible controls for $\sigma$ and $m\ge m_0$. Let a nonterminal state with a failing LP satisfy the memory invariants $h_i=\sum_sA^{(s)}t^{(s)}\gamma^{(s)}_i\ge0$, $H=\sum_ih_i\le L_0$, $mh_i-H\le R_0H$, the column certificate (5.15) with $L_{\mathrm{col}}=9$ and the retained event law of Lemma 5.2, every stored generation having been created by a legal activation law ($t^{(s)}=t$, $\gamma^{(s)}_i<3/m$). For every optimal dual and every choice of pure best responses, the repair of Algorithm 1 (with the activation law and reverse allocations of Lemma 5.5) has total frozen deficit
--   $$0\le E\le\frac{C_Eu}{m}=\frac{120u}{m}\qquad(5.29),$$
--   retains a base coefficient $C_{\mathrm{raw}}/(1+E)\ge c$, gives the certificate law of the new state by thinning (5.23), and satisfies
--   $$\varsigma^+\ge c\varsigma+D-E\qquad(5.30).$$
--
--   Differences from the source:
--   - generalization: a reachable nonterminal failed-LP state → any nonterminal failed-LP state with the memory invariants, the column certificate, the certificate law, and legal stored generations ($t^{(s)}=t$, $\gamma^{(s)}_i<3/m$); reason: Lemma 5.12 shows every reachable state satisfies these; the proof uses exactly them, including (5.31) at each stored generation (p.31)
--   - generalization: an optimal rational dual and the algorithm's best responses → any optimal dual and any pure best responses; reason: the proof uses only optimality; contains the algorithm's choices
--   - reading: auxiliary certificate thinning gives (5.23) → the certificate law (`CertLaw`) of the repaired state; reason: (5.23)'s identities are the update (3.11); the content is the retained law
--   - reading: the retained event law of Lemma 5.2 (disjoint events on an augmented probability space) → `CertLaw` (pointwise domination of the laws, with one domination per opponent override); reason: Lemma 5.2 in measure form; the proofs use only these dominations
--   - generalization: game with rational payoffs in $[0,1]$ → any real game with payoffs in $[0,1]$ (`BoundedGame`); reason: the proof uses only $0\le u_i\le1$; contains the paper's rational games
-- source:
--   J. Tang, S. Ding, C. Fang, Breaking the One-Player Extension Barrier: History-Aware Repair for Multiplayer Approximate Nash Equilibria, arXiv:2611.06076 (preprint; held version, sha256 34b911ed…5c14), Lemma 5.6, (5.29)–(5.30), p.29; proof pp.29–32

import Mathlib
import Definitions.Def_NashAmplification_Filtering_Model
import Definitions.Def_MultiNashRepair_IDRH

open NashAmplification.Filtering (Mixed Utility Tuple BoundedGame)
open Finset

namespace MultiNashRepair

/-- **Lemma 5.6 (A Uniform Bound on the Total Deficit)** (Tang, Ding, Fang, arXiv:2611.06076,
Lemma 5.6, (5.29)–(5.30), p.29; proof pp.29–32).

Fix admissible controls, `m ≥ m0`, and a nonterminal state at which the LP fails, satisfying the
historical memory invariants (5.52)–(5.53), the column-certificate invariant (5.15) with
`Lcol = 9`, and the retained event law of Lemma 5.2, with every stored generation created by a
legal activation law (`t^{(s)} = t`, `γ^{(s)}_i < 3/m`). For every optimal dual and every choice of
pure best responses in the two sweeps, the repair of Algorithm 1 (activation law and reverse
allocation of Lemma 5.5) has total frozen deficit `0 ≤ E ≤ C_E u/m = 120u/m` (5.29); the
correction retains a base coefficient `C_raw/(1 + E) ≥ c`; certificate thinning gives (5.23), i.e.
the certificate law of the new state; and `ς⁺ ≥ cς + D − E` (5.30).

**Formalization Note.** The paper's "reachable state" is replaced by the invariants its proof
uses (Lemma 5.12 shows every reachable state satisfies them, including the legal activation law
of every stored generation, which the proof uses through (5.31) at each stored generation, p.31).
"m ≥ 1000/u²" follows from `m ≥ m0` (5.2). The retained event law is `CertLaw`. -/
theorem lemma_5_6 {σ : ℚ} (ctrl : Controls σ) {m : ℕ} {n : Fin m → ℕ} (hm : ctrl.m0 ≤ m)
    (hn : ∀ i, 0 < n i) (u : Utility n) (hu : BoundedGame u) (s : State n)
    (hx : AGT.IsMixedProfile s.x) (hterm : ¬ Terminal σ u s)
    (hgens : ∀ g ∈ s.gens, GenLegal g ∧ g.t = ctrl.knobs.t ∧ ∀ i, g.γ i < 3 / m)
    (hI1 : ∀ i, s.h i = (s.gens.map fun g => g.A * g.t * g.γ i).sum)
    (hH : s.H = ∑ i, s.h i)
    (hI2 : (∀ i, 0 ≤ s.h i) ∧ s.H ≤ ctrl.knobs.L0 ∧
      ∀ i, (m : ℝ) * s.h i - s.H ≤ ctrl.knobs.R0 * s.H)
    (hI3 : ColumnBound u s.gens 9) (hI4 : CertLaw s.x s.gens)
    (hfail : ¬ Passes ctrl u s)
    (w : (i : Fin m) → Fin (n i) → ℝ) (α : ℝ) (arev acor : (i : Fin m) → Fin (n i))
    (hw : DualOptimal u s.x ctrl.η w α)
    (hrev : IsRevBR u (rY ctrl.knobs s w) (rDelta ctrl.knobs s w) arev)
    (hfwd : IsFwdBR u (rXt ctrl.knobs s w arev) (rE ctrl.knobs u s w arev) acor) :
    let k := ctrl.knobs
    let E := rEtot k u s w arev
    let s' := repairState k u s w arev acor
    0 ≤ E ∧ E ≤ 120 * (ctrl.u : ℝ) / m ∧ k.c ≤ rCraw k s w / (1 + E) ∧
      CertLaw s'.x s'.gens ∧ k.c * scaled u s.x + k.Dsh s.H - E ≤ scaled u s'.x := by sorry

end MultiNashRepair
