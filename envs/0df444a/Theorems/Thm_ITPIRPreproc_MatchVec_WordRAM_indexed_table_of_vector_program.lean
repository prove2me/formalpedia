-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_WordRAM_indexed_table_of_vector_program
-- name    : ITPIRPreproc.MatchVec.WordRAM.indexed_table_of_vector_program
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:41:54.218441+00:00
-- url     : https://prove2.me/theorems/27a9f709-3271-4160-92dd-d93e8063d62f
-- title:
--   Batching indexed vector computations into a linear-space table program
-- statement:
--   Let an indexed deterministic word-RAM program compute the pairs $u_a,v_a$ for a family with $2^h$ rows and dimension $d$, within work $C_0dh^{c_0}$ and workspace $C_0d$ per row. Then there is one deterministic table program, uniform in $h$, which outputs all pairs in row order. For every $h\ge3$ its work is at most
--   $$
--   (C_0+20)\,2^h d\,h^{c_0+4}
--   $$
--   and its working storage is at most $(C_0+20)\,2^h d$.
--
--   This is the batching step in the paper’s table-construction bound. The workspace includes the emitted table itself. A proof must arrange the repeated per-row computation so that only linear-in-the-output temporary storage is used; in particular, retaining exponentially large self-delimiting packages for all intermediate rows is not allowed.
-- source:
--   Dujmovic–Lai–Wichs, STOC 2027 submission #572, Appendix A, printed pp.35–37 (PDF pp.37–39): table construction in $md\,\mathrm{poly}(h)$ time and $O(md)$ space from per-entry computation.

import Definitions.Def_ITPIRPreproc_MatchVec_IndexedVectorComputation
import Mathlib.Tactic

open ITPIRPreproc.MatchVec ITPIRPreproc.MatchVec.WordRAM

theorem ITPIRPreproc.MatchVec.WordRAM.indexed_table_of_vector_program
    (dim : ℕ → ℕ) (u v : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6)
    (C₀ : ℝ) (c₀ : ℕ) (vecProg : Program)
    (hvec : IndexedVectorComputable dim u v C₀ c₀ vecProg) :
    ∃ tableProg : Program, Deterministic tableProg ∧
      ∀ h : ℕ, 3 ≤ h →
        Halts tableProg (encNat h) zeroTape ∧
        output tableProg (encNat h) zeroTape = mvTableCode (u h) (v h) ∧
        (cost tableProg (encNat h) zeroTape : ℝ) ≤
          (C₀ + 20) * 2 ^ h * dim h * (h : ℝ) ^ (c₀ + 4) ∧
        (workingBits tableProg (encNat h) zeroTape : ℝ) ≤
          (C₀ + 20) * 2 ^ h * dim h := by sorry
