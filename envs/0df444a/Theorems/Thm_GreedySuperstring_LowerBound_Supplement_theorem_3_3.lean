-- Prove2me | Theorems.Thm_GreedySuperstring_LowerBound_Supplement_theorem_3_3
-- name    : GreedySuperstring.LowerBound.Supplement.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:39:45.302796+00:00
-- url     : https://prove2.me/theorems/cf212703-2610-49c2-bdd6-8ec456aa90b1
-- title:
--   Theorem 3.3 — the coefficient of $W$ in the cycle-cover inequality is optimal
-- statement:
--   For every real $\gamma<1$ there is a nonempty finite substring-free set $S$ of nonempty binary words such that
--
--   $$O>\mathrm{OPT}+\gamma W,$$
--
--   where $O$ and $W$ are the total cycle-closing overlap and the total prefix of the cycle cover built by the first stage of MGREEDY on $S$, and $\mathrm{OPT}$ is the length of a shortest common superstring of $S$. The inequality holds for every complete run of MGREEDY's first stage on $S$, whatever the tie-breaking, and at least one such run exists.
--
--   Together with Theorem 3.1 this shows that $\gamma=1$ is the smallest coefficient for which the cycle-cover inequality holds on all instances.
--
--   Differences from the source:
--   - encoding: binary strings → words over the published Symbol carrier all of whose symbols are zeroSymbol or oneSymbol; reason: the two distinct one-bit labels are a renaming of {0,1}
--   - encoding: O and W of the cycle cover 𝒞 constructed by MGREEDY on S → existence of a complete run, and the strict inequality for every complete run; reason: the paper's construction allows arbitrary tie-breaking; requiring the inequality for every run and a run to exist excludes a vacuous statement
--   - encoding: a substring-free binary witness satisfying the strict inequality → the witness set is explicitly nonempty; reason: the empty set has O = W = OPT = 0 and cannot satisfy the strict inequality
-- source:
--   Nikolai Chukhin, Rishikesh Gajjala, Juha Harviainen, Alexander S. Kulikov, Ivan Mihajlin, Hiroki Shibata, Alexander V. Smal, The Greedy Superstring Conjecture Is False, STOC 2027 submission #316 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/316.pdf, SHA-256 84e171350ae4e20ed6899c32b480753dae49f7b418819656dfedbcac0f60e8fa, Theorem 3.3, printed p.12 = PDF p.12; proof pp.12–13

import Mathlib
import Definitions.Def_GreedySuperstring_LowerBound_GapModel
import Definitions.Def_GreedySuperstring_LowerBound_Supplement_CycleCover

namespace GreedySuperstring.LowerBound.Supplement

open GreedySuperstring.LowerBound

/-- Theorem 3.3, printed/PDF p.12. For every real `γ < 1` there is a finite substring-free set
`S` of nonempty binary words on which MGREEDY's first stage has a complete run, and every
complete run (every tie-breaking) satisfies `O > OPT + γW`. -/
theorem theorem_3_3 (γ : ℝ) (hγ : γ < 1) :
    ∃ S : Finset OAI.Superstring.Word,
      S.Nonempty ∧ (∀ s ∈ S, IsBinary s ∧ s ≠ []) ∧ SubstringFree S ∧
      (∃ reps, IsCycleCoverRun S reps) ∧
      ∀ reps, IsCycleCoverRun S reps →
        ((totalOverlap reps : ℕ) : ℝ) >
          ((OAI.Superstring.opt S.toList : ℕ) : ℝ) + γ * ((totalPrefix reps : ℕ) : ℝ) := by sorry

end GreedySuperstring.LowerBound.Supplement
