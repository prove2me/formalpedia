-- Prove2me | Theorems.Thm_IntervalMaxCutEPTAS_Scheme_Supplement_lemma_7_3
-- name    : IntervalMaxCutEPTAS.Scheme.Supplement.lemma_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:34:38.590018+00:00
-- url     : https://prove2.me/theorems/cc66a0ec-3b66-4adf-aeaf-c3c8dc1535e1
-- title:
--   Lemma 7.3 (used in the proof of Theorem 1.3) — chordality and elimination order
-- statement:
--   For every simple source graph $Q$ with at least one edge and every integer $p\ge1$, the entire attachment graph $T_p(Q)$ is chordal. Deleting precisely its private vertices leaves a split graph. Every private vertex has exactly the two designated neighbors, its core and middle, and those neighbors are adjacent:
--
--   $$N_{T_p(Q)}(x)=\{c_v^i,a_v^{i,j}\},\qquad \deg(x)=2.$$
--
--   One deterministic program, fixed before $Q,p$, computes an actual perfect elimination ordering from the ordinary source adjacency matrix and $p$, in time and space polynomial in $n_Q+p+1$. An ordering means a permutation of all target vertices whose later neighbors form a clique. The lemma places the reduction's outputs in the restricted target class of Theorem 1.3.
--
--   Differences from the source:
--   - encoding: finite vertices and one-based copy and repetition indices → Fin n, Fin 2, and Fin p; dependent private indices; reason: these are bijective renamings, with exactly the source number of vertices and no padding
--   - encoding: a polynomially computable perfect elimination ordering → a uniform charged Light program returning a full permutation in fixed target vertex names, with the actual PEO property; reason: finite source input and fixed target naming make the algorithmic conclusion concrete; polynomial time also bounds space
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), Lemma 7.3, PDF p. 26 (printed p. 25)

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Supplement_Gadget

set_option autoImplicit false

namespace IntervalMaxCutEPTAS.Scheme.Supplement

/-- Lemma 7.3, PDF 26 (printed 25). All private vertices occur, with exactly their two
specified neighbors, and the machine returns an actual perfect elimination ordering. -/
theorem lemma_7_3 :
    ∃ (Prog : Light.Program) (C d c : ℕ), 0 < C ∧ 1 ≤ d ∧ 1 ≤ c ∧
      ∀ (n : ℕ) (Q : SimpleGraph (Fin n)) [DecidableRel Q.Adj] (p : ℕ),
        1 ≤ Q.edgeFinset.card → 1 ≤ p →
        GavrilSubtree.Chordal.IsChordal (target Q p) ∧
        IsSplit ((target Q p).induce {x | x ∉ privateSet Q p}) ∧
        (∀ (a : Attachment n p) (t : Fin (Q.degree a.vertex + 1)),
          (target Q p).degree (privateVertex Q p a t) = 2 ∧
          (target Q p).Adj (core Q p a.copy a.vertex) (middle Q p a) ∧
          (target Q p).neighborFinset (privateVertex Q p a t) =
            {core Q p a.copy a.vertex, middle Q p a}) ∧
        ∃ T S : ℕ, T ≤ C * (n + p + 1) ^ d ∧ S ≤ C * (n + p + 1) ^ d ∧
          Light.Ends ⟨((n + p + 2) ^ c : ℕ), S, T⟩ Prog 0 entry
            (start (encodePEO Q p)) T (ReportsPEO Q p S) := by sorry

end IntervalMaxCutEPTAS.Scheme.Supplement
