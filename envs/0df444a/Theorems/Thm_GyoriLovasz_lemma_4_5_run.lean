-- Prove2me | Theorems.Thm_GyoriLovasz_lemma_4_5_run
-- name    : GyoriLovasz.lemma_4_5_run
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:54:35.503263+00:00
-- url     : https://prove2.me/theorems/63412bb0-f64b-482d-b3a7-a1aa453c39de
-- title:
--   Lemma 4.5 — ShiftAssignment finds a removable non-critical edge (correctness and shift bound; time bound: theorem_2; corrected: G nonempty)
-- statement:
--   Let $G=(V,E)$ be a directed graph with at least one vertex, terminal set $T\subseteq V$, no self-loops and no edge leaving a terminal, and let $\varphi$ be a flow-essential assignment for capacities $c$ with $c_t>0$ for all $t\in T$ and $d^+(x)\ge2$ for every pre-terminal $x$. Then:
--
--   1. lines 1–2 of Algorithm 3 can be carried out: a matching $p$ from pre-terminals to terminals and secondary edges $e_t$ exist;
--   2. for every such choice of $p$ and $e$, and every run of the while loop that performs $n$ shifts from $\varphi$ to $\varphi_1$ (on any sequence of choices),
--   $$n\le k\,|V\setminus T|,$$
--   $\varphi_1$ is again a flow-essential assignment, and either some $e_t$ is non-critical for $\varphi_1$ (the loop exits) or a further shift can be performed;
--   3. if $e_t$ is non-critical for a flow-essential assignment $\varphi_1$, then $\varphi_1$ is a flow-essential assignment of $G\setminus e_t$ for the same capacities.
--
--   Together, the clauses say that ShiftAssignment terminates on every sequence of choices, after at most $k|V\setminus T|$ shifts, and returns $\varphi'$ and $e_{\mathrm{nc}}$ with $(G\setminus e_{\mathrm{nc}},T,c,\varphi')$ satisfying the Flow-Essential Assignment Condition.
--
--   Differences from the source:
--
--   - reading: "ShiftAssignment terminates in polynomial time" → every partial run of the loop on every sequence of choices has at most k|V ∖ T| shifts (the bound of p.32) and can be continued or exited; no running time; reason: the procedure is idealized, with no machine model; the machine cost is carried by theorem_2 (paper.md decision 9)
--   - correction: no condition on G → hypothesis G.verts.Nonempty; reason: on the empty graph with T = ∅ every hypothesis holds (the empty assignment is flow-essential, the conditions on c and d⁺ are vacuous) but there is no edge e_nc to return; Algorithm 2 calls the lemma only after line 1 fails
--   - encoding: ShiftAssignment returns an assignment φ′ and an edge e_nc → ShiftChain (a relation recording every free choice of lines 1–13) and IsNonCritical for the exit of lines 4–6; reason: a statement over all chains covers every execution
--   - encoding: the standing assumption of §2, p.14: terminals are vertices, no self-loops or parallel edges, terminals have no outgoing edges (stated once, "without loss of generality") → explicit hypotheses `Std G T` and `T ⊆ G.verts`; parallel edges are impossible in `DG`; reason: trap 19: a section's standing assumption is a hypothesis of each of its results
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Lemma 4.5, p.28; proof of Lemma 4.5, pp.31–32

import Mathlib
import Definitions.Def_GyoriLovasz_IsWitness
import Definitions.Def_GyoriLovasz_IsTermMatching
import Definitions.Def_GyoriLovasz_PT
import Definitions.Def_GyoriLovasz_ShiftChain
import Definitions.Def_GyoriLovasz_Std

namespace GyoriLovasz

variable {V : Type*} [DecidableEq V]

/-- **Lemma 4.5, correctness and iteration bound (time bound: `theorem_2`).** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Lemma 4.5, p.28: "Let (G, T, c, φ) satisfy the Flow-Essential
Assignment Condition. Assume that c_i > 0 for every i ∈ [k], and that d⁺(v) ≥ 2 for every pre-terminal v ∈ PT(G, T). Then ShiftAssignment terminates
in polynomial time and returns an assignment φ′ and an edge e_nc such that (G \ e_nc, T, c, φ′) satisfies the Flow-Essential Assignment Condition."

Lines 1–2 can be carried out: a matching and secondary edges exist. For any such choice, every partial run of the loop with `n` shifts has
`n ≤ k|V \ T|` (p.32), and reaches a witness `φ₁` at which either some `e_t` is non-critical for `φ₁` (the exit of lines 4–6) or another shift is
available. A secondary edge that is non-critical for a witness can be deleted, with the same witness.

**Formalization Note.** Together the clauses say that the loop terminates on every sequence of choices with the printed output. The machine cost
is carried by `theorem_2`. `G.verts.Nonempty` is the failure of line 1 of Algorithm 2: on the empty graph there is no edge to return. `Std`
and `T ⊆ V` are the standing assumptions of §2. -/
theorem lemma_4_5_run (G : DG V) (T : Finset V) (c : V → ℕ) (φ : V → V) (hstd : Std G T)
    (hT : T ⊆ G.verts) (hG : G.verts.Nonempty) (hw : IsWitness G T c φ) (hc : ∀ t ∈ T, 0 < c t)
    (hd : ∀ x ∈ PT G T T, 2 ≤ G.outDeg x) :
    (∃ p sec, IsTermMatching G T p ∧ IsSecondary G T p sec) ∧
      ∀ p sec, IsTermMatching G T p → IsSecondary G T p sec →
        (∀ φ₁ n, ShiftChain G T sec φ n φ₁ →
          n ≤ T.card * (G.verts \ T).card ∧ IsWitness G T c φ₁ ∧
            ((∃ t ∈ T, IsNonCritical G T (sec t) φ₁) ∨ ∃ φ₂, ShiftChain G T sec φ₁ 1 φ₂)) ∧
        ∀ t ∈ T, ∀ φ₁, IsWitness G T c φ₁ → IsNonCritical G T (sec t) φ₁ →
          IsWitness (G.deleteArc (sec t)) T c φ₁ := by sorry

end GyoriLovasz
