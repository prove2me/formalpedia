-- Prove2me | Theorems.Thm_LocalProbeMIS871_Greedy_Supplement_lemma_4_1
-- name    : LocalProbeMIS871.Greedy.Supplement.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:03:37.362818+00:00
-- url     : https://prove2.me/theorems/3dc4e999-6fb0-45c2-802e-4dfbea115ada
-- title:
--   Lemma 4.1 — Simultaneous undominated vertices and vanishing error
-- statement:
--   Let $D_0$ be the graph experiment of §4.1, with degree parameter $\Delta$, admissible clique count $m$, hidden independent set $A$ of size $N$, and $B$ partitioned into prescribed cliques $C_j$ of size $k$. There is an absolute $c_*>0$ such that for every sufficiently large $\Delta$ and then every sufficiently large admissible $m$,
--
--   $$\Pr_{D_0}\left[\forall S\subseteq B,\ \bigl(\forall j,\ |S\cap C_j|\le1\bigr)\Longrightarrow |A\setminus N_G(S)|\ge N/4\right]\ge1-\eta_{c_*}(\Delta,m),$$
--
--   where $N_G(S)$ is the union of open neighborhoods and $\eta_{c_*}(\Delta,m)=\exp(m\ln(k+1)-c_*N)$. For each sufficiently large fixed $\Delta$, this same error tends to zero as $m\to\infty$ through every admissible choice. The threshold for $m$ may depend on $\Delta$; the positive constant and degree threshold precede both inputs.
--
--   The event is simultaneous over selections made after the graph has been sampled. It supplies the structural separation used by the companion lower bound.
--
--   **Formalization Note** The existential witness is explicitly selected as $1/2304$ using Eq. (40), not printed as a numerical constant in the lemma. The convergence clause is written in its equivalent epsilon-and-integer-threshold form along all admissible $m$.
--
--   Differences from the source:
--   - encoding: vertices labeled in [n] → vertices represented by Fin n; reason: adding one to each label is a bijection and preserves all graph and oracle information
--   - encoding: the finite distributions D₀ and D₁ of §4.1 → uniform counting on finite permutation seeds followed by the specified graph, list and query maps; reason: all fibers have constant multiplicity, so these are exactly the source laws, with no conditioning
--   - encoding: an unspecified positive absolute c_* in η → the existential witness c_*=1/2304 from Eq. (40), shared by both lemmas; reason: h≤2N makes (N/12)^2/(8h)≥N/2304; this selects a witness without dropping any instance
--   - encoding: η tends to zero along admissible m → for every ε>0, eventually |η|<ε for every admissible integer m; reason: this is precisely convergence on the source index domain
-- source:
--   Peter Kiss, Yuichi Yoshida, The Local Probe Complexity of Maximal Independent Set, STOC 2027 submission #871 (October 2026), p. 25, PDF p. 27, Lemma 4.1

import Definitions.Def_LocalProbeMIS871_Greedy_Supplement_Observation

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false

namespace LocalProbeMIS871.Greedy.Supplement

/-- Lemma 4.1, printed p.25 / PDF27, including convergence along all admissible m.
The equality selects the source-derived witness from Eq.(40), not a changed bound. -/
theorem lemma_4_1 :
    ∃ c : ℝ, 0 < c ∧ c = cStar ∧ ∃ Δ₀ : ℕ, 2 ≤ Δ₀ ∧ ∀ Δ : ℕ, Δ₀ ≤ Δ →
      (∃ M : ℕ, ∀ m : ℕ, M ≤ m → Admissible Δ m →
        1 - eta c Δ m ≤ finiteProb (fun s : Seed Δ m => selectionGood s)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → Admissible Δ m →
        |eta c Δ m| < ε) := by sorry

end LocalProbeMIS871.Greedy.Supplement
