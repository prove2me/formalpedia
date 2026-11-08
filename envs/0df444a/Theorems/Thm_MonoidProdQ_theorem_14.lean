-- Prove2me | Theorems.Thm_MonoidProdQ_theorem_14
-- name    : MonoidProdQ.theorem_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:59:18.018543+00:00
-- url     : https://prove2.me/theorems/d505d8b4-36d0-47c3-96df-64fcbea28e39
-- title:
--   Theorem 14 (Essential-width adversary theorem): $\mathrm{ADV}^{\pm}(f)\le16\sqrt{nB}$
-- statement:
--   Let $I$ be a finite index set with $|I|=n\ge1$, $\Sigma$ and $O$ finite alphabets, $D\subseteq\Sigma^I$ a nonempty promise domain and $f$ a function on $D$ with values in $O$. Suppose $f$ has an incremental summary with finite state set $Q$ whose essential width is at most a real number $B\ge0$. Then:
--
--   1. the adversary bound satisfies
--   $$\mathrm{ADV}^{\pm}(f)\le16\sqrt{nB};$$
--   2. there is a universal constant $C>0$, independent of $I,\Sigma,O,Q,D,f,B$, with
--   $$Q_{1/3}(f)\le C\sqrt{nB};$$
--   3. if the essential width is zero (every $\mathrm{Ess}_x(T)$ is empty for $x\in D$), then $f$ is constant on $D$ and $\mathrm{ADV}^{\pm}(f)=Q_{1/3}(f)=0$.
--
--   The theorem turns a combinatorial bound on how many revealed positions can still matter into a quantum query upper bound, with an explicit constant and no logarithmic loss.
--
--   Differences from the source:
--   - reading: Consequently $Q_{1/3}(f)=O(\sqrt{nB})$ → one constant $C>0$ chosen before $I,\Sigma,O,Q,D,f,B$; reason: the consequence comes from Eq. (2), whose implicit constants are universal
--   - encoding: $\mathrm{ADV}^{\pm}$ and $Q_{1/3}$ as numbers → `ADV±` in `ℝ≥0∞`, $Q_{1/3}$ in `ℕ∞` (cast to `ℝ≥0∞`); reason: Lean convention; suprema and infima are never junk values, and both are finite in every instance
--   - encoding: a query to index $i$ returns the entire letter $x_i$ → the platform's standard oracle $|i,y\rangle\mapsto|i,y+e_{x_i}\rangle$ with the one-hot code $e_{x_i}\in(\mathbb Z/2)^\Sigma$; reason: the paper fixes no encoding; injective encodings change query counts by at most a factor two, absorbed by the universal constants
--   - encoding: $n=|I|$ → `Fintype.card I`; reason: Lean convention; same quantity
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 14 (Essential-width adversary theorem), p.27

import Definitions.Def_MonoidProdQ_IncrementalSummary_HasEssWidthLE
import Definitions.Def_MonoidProdQ_advPm
import Definitions.Def_MonoidProdQ_Q13

open scoped ENNReal

universe u v w x

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 14 (Essential-width adversary theorem), p.27, in the setting of Definition 2
(finite `I` with `|I| = n ≥ 1`, finite input and output alphabets, a nonempty promise domain
`D`, a finite state set `Q`): "If f has an incremental summary on n ≥ 1 input positions of
essential width at most B ≥ 0, then ADV±(f) ≤ 16√(nB). Consequently Q_{1/3}(f) = O(√(nB)). If
the essential width is zero, f is constant and ADV±(f) = Q_{1/3}(f) = 0." All three clauses:
(i) the adversary bound with the constant 16; (ii) the query bound with one universal constant
`C`, chosen before all the data; (iii) the zero-width case.

**Formalization Note.** `n` is `Fintype.card I`. `ADV±` is in `ℝ≥0∞` and `Q_{1/3}` in `ℕ∞`
(cast to `ℝ≥0∞`). -/
theorem theorem_14 :
    (∀ (I : Type u) (Sig : Type v) (Out : Type w) (Q : Type x) [Fintype I] [DecidableEq I]
      [Fintype Sig] [DecidableEq Sig] [Fintype Out] [DecidableEq Out] [Fintype Q]
      [DecidableEq Q] (f : (I → Sig) → Out) (D : Finset (I → Sig))
      (S : IncrementalSummary f D Q) (B : ℝ),
      1 ≤ Fintype.card I → D.Nonempty → 0 ≤ B → S.HasEssWidthLE B →
      advPm f D ≤ ENNReal.ofReal (16 * Real.sqrt (Fintype.card I * B))) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ (I : Type u) (Sig : Type v) (Out : Type w) (Q : Type x) [Fintype I] [DecidableEq I]
        [Fintype Sig] [DecidableEq Sig] [Fintype Out] [DecidableEq Out] [Fintype Q]
        [DecidableEq Q] (f : (I → Sig) → Out) (D : Finset (I → Sig))
        (S : IncrementalSummary f D Q) (B : ℝ),
        1 ≤ Fintype.card I → D.Nonempty → 0 ≤ B → S.HasEssWidthLE B →
        (Q13 f D : ℝ≥0∞) ≤ ENNReal.ofReal (C * Real.sqrt (Fintype.card I * B))) ∧
    (∀ (I : Type u) (Sig : Type v) (Out : Type w) (Q : Type x) [Fintype I] [DecidableEq I]
      [Fintype Sig] [DecidableEq Sig] [Fintype Out] [DecidableEq Out] [Fintype Q]
      [DecidableEq Q] (f : (I → Sig) → Out) (D : Finset (I → Sig))
      (S : IncrementalSummary f D Q),
      1 ≤ Fintype.card I → D.Nonempty → (∀ y ∈ D, ∀ T : Finset I, S.ess y T = ∅) →
      (∀ y ∈ D, ∀ z ∈ D, f y = f z) ∧ advPm f D = 0 ∧ Q13 f D = 0) := by sorry

end MonoidProdQ
