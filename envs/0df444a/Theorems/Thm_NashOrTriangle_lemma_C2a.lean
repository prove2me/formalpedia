-- Prove2me | Theorems.Thm_NashOrTriangle_lemma_C2a
-- name    : NashOrTriangle.lemma_C2a
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:45:19.85899+00:00
-- url     : https://prove2.me/theorems/4a60a00e-2fdd-4762-8b3e-1a10ccf3f068
-- title:
--   Lemma C.2(a) — no $t$-triangle ⇒ rows and columns have VC dimension $\le t-1$
-- statement:
--   Let $H$ be a binary game with no $t$-triangle. Then the class of rows, viewed as $\{0,1\}$-valued functions on the columns, and the class of columns, viewed as functions on the rows, both have VC dimension at most $t - 1$:
--   $$
--   \mathrm{VC}\{\, b \mapsto M(a, b) : a \in A \,\} \le t - 1, \qquad \mathrm{VC}\{\, a \mapsto M(a, b) : b \in B \,\} \le t - 1 .
--   $$
--   Through uniform convergence for VC classes this gives the sparsification bound (22) for binary games.
--
--   **Formalization Note** Uses the published VC dimension `NatureSLT.GrowthFunction.vcDim` (values in $\mathbb N \cup \{\infty\}$); a row is the indicator $b \mapsto [M(a, b) = 1]$. $t - 1$ is natural-number subtraction; at $t = 0$ the hypothesis fails, since the empty triangle always exists.
--
--   Differences from the source:
--   - encoding: the class of rows viewed as functions on columns (and columns on rows) → the Bool-valued families a ↦ (b ↦ decide (M a b = 1)) and b ↦ (a ↦ decide (M a b = 1)) with NatureSLT vcDim in ℕ∞; reason: in a binary game these indicators are the payoff functions
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), Appendix C, Lemma C.2(a), p.24 (PDF p.25)

import Mathlib
import Definitions.Def_NatureSLT_GrowthFunction_vcDim
import Definitions.Def_NashOrTriangle_IsBinary
import Definitions.Def_NashOrTriangle_HasTriangle

namespace NashOrTriangle

/-- **Lemma C.2(a)** (triangles bound VC dimension). Let `H` be a binary game with no `t`-triangle.
The class of rows, viewed as functions on columns, and the class of columns, viewed as functions
on rows, both have VC dimension at most `t − 1`.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Appendix C, Lemma C.2(a), printed p. 24 (PDF p. 25).

**Formalization Note** Uses the published `NatureSLT.GrowthFunction.vcDim` (values in `ℕ∞`); a
row `a` is the indicator `b ↦ [M(a, b) = 1]`. `t − 1` is natural subtraction; at `t = 0` the
hypothesis fails (the empty triangle always exists). -/
theorem lemma_C2a {A B : Type} [Countable A] [Countable B] [Nonempty A] [Nonempty B]
    (M : A → B → ℚ) (t : ℕ) (hM : IsBinary M) (hT : ¬ HasTriangle M t) :
    NatureSLT.GrowthFunction.vcDim (fun (a : A) (b : B) => decide (M a b = 1)) ≤ ((t - 1 : ℕ) : ℕ∞) ∧
    NatureSLT.GrowthFunction.vcDim (fun (b : B) (a : A) => decide (M a b = 1)) ≤ ((t - 1 : ℕ) : ℕ∞) := by sorry

end NashOrTriangle
