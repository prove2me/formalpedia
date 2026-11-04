-- Prove2me | Theorems.Thm_OAI_RyserCoveringCounterexample_LineCover_uniform_linecover_probability_oddExt
-- name    : OAI.RyserCoveringCounterexample.LineCover.uniform_linecover_probability_oddExt
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-03T23:19:50.389387+00:00
-- url     : https://prove2.me/theorems/491c5520-7b7e-4a05-80d1-f424af959bad
-- title:
--   Line covers after random deletions
-- statement:
--   Fix a positive integer $D$, reals $\delta,\rho>0$ and $\eta>0$. There is a threshold $Q$ such that the following holds for every finite field $F$ with $q=|F|\ge Q$ all of whose proper subfields $M$ satisfy $|M|^3\le q$, and for every deletion process on $F^2$ with parameters $D,\delta$.
--
--   Such a process consists of at most $Dq^D$ shapes in $F^2$, each with at most $Dq$ points, and each meeting any different affine line in at most $D$ points, together with at most $Dq$ independent trials, each selecting at most $D$ shapes. Each trial deletes a given point with probability at most $D/q$; each point survives all trials with the same probability, which is at least $\delta$; and for each affine line $\ell$, the probabilities that the trials list exactly the shape $\ell$ sum to at most $D/q$. Let $X$ be the surviving set, and let $X^\ell$ be the surviving set when exact occurrences of the shape $\ell$ are ignored.
--
--   Then with probability at least $1-\eta$, both of the following hold:
--
--   $$
--   |X^\ell\cap\ell|\ \ge\ \tfrac{\delta q}{2}\quad\text{for every affine line }\ell,
--   $$
--
--   and every set $L$ of at most $q$ affine lines leaving at most $2q$ points of $X$ uncovered contains at least $(1-\rho)q$ lines through a common projective point.
--
--   This is Lemma 3.2 of the paper, in a form uniform over the field and the process. It is the source of the rigidity of small covers: the ordinary edges of the hypergraph force any cover of size at most $q$ to contain almost a full pencil.
-- source:
--   OpenAI, A counterexample to Ryser's covering conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-Rysers-Covering-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lemma 3.2. Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Ryser/LineCover/Main.lean#L68 (declaration OAI.RyserCoveringCounterexample.LineCover.uniform_linecover_probability; suffix _oddExt added for name uniqueness)

import Mathlib
import Definitions.Def_RyserOddSupport

namespace OAI

open Filter Topology
open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

universe u

theorem uniform_linecover_probability_oddExt (D : ℕ) (δ ρ : ℝ)
    (hD : 0 < D) (hδ : 0 < δ) (hρ : 0 < ρ) (η : ℝ) (hη : 0 < η) :
    ∃ Q : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      Q ≤ Fintype.card F → Incidence.SmallProperSubfields F →
      ∀ process : DeletionProcess F D δ,
        1 - η ≤ process.law.prob (GoodLineCover δ ρ) := by
  sorry

end RyserCoveringCounterexample.LineCover
end
end OAI
