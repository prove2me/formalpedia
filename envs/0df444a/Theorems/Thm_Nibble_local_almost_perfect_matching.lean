-- Prove2me | Theorems.Thm_Nibble_local_almost_perfect_matching
-- name    : Nibble.local_almost_perfect_matching
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-24T12:55:10.035589+00:00
-- url     : https://prove2.me/theorems/9ab1ec51-a300-4dc1-b374-3571a8808a87
-- title:
--   Local almost-perfect matchings via the nibble
-- statement:
--   A local, weighted form of the almost-perfect matching theorem for hypergraphs with small codegrees. It is proved with the Rödl nibble.
--
--   **Setting.** Let $J$ (jobs), $S$ (slots) and $O$ (options) be finite sets. Each option $o$ belongs to one job $j(o)$ and uses a set $s(o)\subseteq S$ of at most two slots. Some options are marked as *dummy*. A dummy option uses private slots: its slots are disjoint from the slots of every other option. Let $x\colon O\to[0,\infty)$ be fractional weights, and let $\sigma,\kappa>0$. Assume:
--
--   1. every job has total weight one: $\sum_{o:\,j(o)=e}x_o=1$ for every $e\in J$;
--   2. every slot has spare capacity: $\sum_{o:\,t\in s(o)}x_o\le 1-\sigma$ for every $t\in S$;
--   3. the codegrees are small: $\sum_{o:\,j(o)=e,\ t\in s(o)}x_o\le\kappa$ for every job $e$ and slot $t$, and $\sum_{o:\,s,t\in s(o)}x_o\le\kappa$ for all distinct slots $s\ne t$.
--
--   Further, let $G$ be a finite set of *groups*. Each group $g$ is a set $J_g\subseteq J$ of jobs, and each job $e$ has a weight $w_e\in[0,1]$. Let $D\ge1$ be an integer that bounds each of the following:
--
--   - the number of jobs $f$ (counting $e$ itself) that have an option sharing a slot with an option of $e$;
--   - the number of jobs using any given slot;
--   - the number of slots used by the options of any given job;
--   - the size $|J_g|$ of every group;
--   - the number of groups containing any given job.
--
--   **Statement.** For all $\sigma,\varepsilon\in(0,1]$ there are constants $c_1>0$ and $c_2$, depending only on $\sigma$ and $\varepsilon$, with the following property. Suppose all the data above satisfy
--
--   $$
--   \kappa\,(\log D+1)\le c_1\qquad\text{and}\qquad \kappa^2D\,(\log D+1)\le c_1 .
--   $$
--
--   Then there is a set $M$ of options with the following properties:
--
--   1. every option in $M$ has positive weight;
--   2. distinct options in $M$ belong to distinct jobs and use disjoint slot sets;
--   3. in every group $g$, the weight of the jobs not covered by a non-dummy option of $M$ satisfies
--
--   $$
--   \sum_{\substack{e\in J_g\\ e\text{ not covered}}} w_e\ \le\ \sum_{e\in J_g} w_e\Bigl(1-\sum_{\substack{o:\,j(o)=e\\ o\text{ not dummy}}}x_o\Bigr)+\varepsilon\sum_{e\in J_g}w_e+c_2\Bigl(\sqrt{|J_g|\,(\log D+1)}+\log D+1\Bigr).
--   $$
--
--   In words, the uncovered weight in each group is at most the weight that the fractional solution leaves to dummy options, plus an $\varepsilon$ fraction, plus a lower-order error term.
--
--   **Role.** This is a local, weighted version of the Pippenger–Spencer almost-perfect matching theorem, in the form Kahn used for asymptotic list edge colouring, for hypergraphs whose edges are a job together with at most two slots. In Gajjala–Khan's proof of Theorem 3.1, the step *Rounding the large edges* turns fractional options of the large edges into whole options. This lemma can be used for that step in place of Proposition A.5: jobs are large edges, slots are the (vertex, colour, slot-index) triples, dummy options absorb the unassigned fraction $1-s_e$, and groups are the sets of large edges at each vertex.
--
--   **Formalization Note.** Options are given by functions `job : O → J` and `sl : O → Finset Sl`, and dummy options by a decidable predicate `dum`. The degree bound $D$ is a natural number, and $\log$ is the real natural logarithm. A job is *covered* if some option $m\in M$ satisfies `job m = e` and `¬ dum m`. The first counted set in the $D$-hypotheses is written `insert e (filter …)`.
-- source:
--   Rödl nibble in the form of J. Kahn, Asymptotically good list-colorings, J. Combin. Theory Ser. A 73 (1996) 1-59, §§3-4 (cf. N. Pippenger, J. Spencer, Asymptotic behavior of the chromatic index for hypergraphs, JCTA 51 (1989)); local weighted form stated for the step 'Rounding the large edges' in R. Gajjala, A. Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, arXiv:2611.03190, proof of Theorem 3.1, pp.40-42, as a replacement for Proposition A.5 (p.26)

import Mathlib
open Finset

theorem Nibble.local_almost_perfect_matching (σ ε : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧
      ∀ (J Sl O G : Type) [Fintype J] [DecidableEq J] [Fintype Sl] [DecidableEq Sl]
        [Fintype O] [DecidableEq O] [Fintype G] [DecidableEq G]
        (job : O → J) (sl : O → Finset Sl) (dum : O → Prop) [DecidablePred dum]
        (memb : G → Finset J) (w : J → ℝ) (x : O → ℝ) (κ : ℝ) (D : ℕ),
        (∀ o, (sl o).card ≤ 2) →
        (∀ o, dum o → ∀ o', o' ≠ o → Disjoint (sl o) (sl o')) →
        (∀ e, 0 ≤ w e ∧ w e ≤ 1) → (∀ o, 0 ≤ x o) →
        (∀ e, ∑ o ∈ univ.filter (fun o => job o = e), x o = 1) →
        (∀ s, ∑ o ∈ univ.filter (fun o => s ∈ sl o), x o ≤ 1 - σ) →
        (∀ e t, ∑ o ∈ univ.filter (fun o => job o = e ∧ t ∈ sl o), x o ≤ κ) →
        (∀ s t, s ≠ t → ∑ o ∈ univ.filter (fun o => s ∈ sl o ∧ t ∈ sl o), x o ≤ κ) →
        0 < κ → 1 ≤ D →
        (∀ e, (insert e (univ.filter (fun f => ∃ o o', job o = e ∧ job o' = f ∧
            ¬ Disjoint (sl o) (sl o')))).card ≤ D) →
        (∀ s, (univ.filter (fun e => ∃ o, job o = e ∧ s ∈ sl o)).card ≤ D) →
        (∀ e, (univ.filter (fun s => ∃ o, job o = e ∧ s ∈ sl o)).card ≤ D) →
        (∀ g, (memb g).card ≤ D) →
        (∀ e, (univ.filter (fun g => e ∈ memb g)).card ≤ D) →
        κ * (Real.log D + 1) ≤ c₁ →
        κ ^ 2 * D * (Real.log D + 1) ≤ c₁ →
        ∃ M : Finset O, (∀ o ∈ M, 0 < x o) ∧
          (∀ o ∈ M, ∀ o' ∈ M, o ≠ o' → job o ≠ job o' ∧ Disjoint (sl o) (sl o')) ∧
          ∀ g, ∑ e ∈ memb g, w e * (if ∃ m ∈ M, job m = e ∧ ¬ dum m then 0 else 1) ≤
            ∑ e ∈ memb g, w e * (1 - ∑ o ∈ univ.filter (fun o => job o = e ∧ ¬ dum o), x o) +
              ε * ∑ e ∈ memb g, w e +
              c₂ * (Real.sqrt ((memb g).card * (Real.log D + 1)) + (Real.log D + 1)) := by sorry
