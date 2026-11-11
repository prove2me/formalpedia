-- Prove2me | Theorems.Thm_LeakageRefresh_Continual_lemma_4_15
-- name    : LeakageRefresh.Continual.lemma_4_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:11:39.49787+00:00
-- url     : https://prove2.me/theorems/ffb1e289-ce46-4b17-8834-75d4f4dfc840
-- title:
--   Lemma 4.15 — replacing one valid round by its approximation costs $\mathbb E|e\cdot G'|\le6\varepsilon$, and $\varepsilon$ with no signed companion
-- statement:
--   Let $n\ge2$. Fix the leakage functions and answer of a valid round, with table $\mathrm{prob}$, and its approximation $G$, which satisfies $\|\mathrm{prob}-G\|_{2,\mu_s\otimes\mu_s}\le\varepsilon$ for both $s$ (Eq. (4.63)); let $G'$ be the approximation of the neighbouring signed round, with $\|G'\|_{2,\mu_s\otimes\mu_{s'}}\le6$ for all label pairs (Eq. (4.64)). Let $e=\mathrm{prob}-G$. Sample $A$, $X$, $B$ independently from the encoding distributions of their labels. If round $j$ (states $A,X$, common label $s$) is valid and round $j+1$ is signed with companion $G'(X,B)$, then
--   $$\mathbb E_{A,X,B}\big[|e(A,X)\cdot G'(X,B)|\big]\le6\varepsilon. \tag{4.65}$$
--   The same estimate holds when the valid error is $e(X,B)$ (common label of $X,B$) and the companion is $G'(A,X)$. For a valid round with no signed companion, $\mathbb E_{A,X}|e(A,X)|\le\varepsilon$.
--
--   Differences from the source:
--   - generalization: $G$, $G'$ are the approximations of Lemma 4.13 at rounds $j$, $j+1$ ($j\in\{1,\dots,T-1\}$) → any tables $G$ with (4.63) for the given round's table and $G'$ with (4.64); reason: the proof uses only (4.63) and (4.64); the tables of Lemma 4.13 satisfy both, so the statement specializes to the paper's
--   - encoding: a fixed formal incoming history and adversary tape (which fix the two leakage functions) → an arbitrary pair of leakage functions `lp : LeakPair n lam`; reason: every pair of leakage functions arises from some strategy, history and tape, and conversely
--   - encoding: $\mathbb E_{A,X,B}$ with $A\leftarrow\mu_{s_{j-1}}$, $X\leftarrow\mu_{s_j}$, $B\leftarrow\mu_{s_{j+1}}$ independent → finite sums weighted by the point probabilities `mu n s`; reason: expectations over finite distributions written as weighted sums
-- source:
--   Dziembowski, Faust, Leakage-Resilient Computation via Matrix Refreshing, arXiv:2611.04876 (sha256 fdbb2454…), p. 42, Lemma 4.15

import Mathlib
import Definitions.Def_LeakageRefresh_Continual_Encoding
import Definitions.Def_LeakageRefresh_Continual_LeakageModel
import Definitions.Def_LeakageRefresh_Continual_Tables
import Definitions.Def_LeakageRefresh_Continual_OneRound

namespace LeakageRefresh.Continual

/-- **Lemma 4.15 (Replacing one round).** Let `prob = prob_z` be the table of a valid round
(leakage functions `lp`, answer `z`) and `G` a table with `‖prob − G‖_{2,µₛ⊗µₛ} ≤ ε` for both
`s` (Eq. (4.63)); let `G′` be a table with `‖G′‖_{2,µₛ⊗µₛ′} ≤ 6` for all label pairs
(Eq. (4.64)). With `e = prob − G` and `A, X, B` independent with the stated labels:
(4.65) `E_{A,X,B}|e(A, X) · G′(X, B)| ≤ 6ε` when round `j` (states `A, X`, common label `s`) is
valid; the same when the valid error is `e(X, B)` (common label `s`) and the companion is
`G′(A, X)`; and `E|e(A, X)| ≤ ε` for a valid round with no signed companion. -/
theorem lemma_4_15 (n lam : ℕ) (hn : 2 ≤ n) (lp : LeakPair n lam) (z : Answer lam)
    (G G' : Table4 n) (ε : ℝ)
    (hG : ∀ s : ZMod 2, rmsMu n s s (fun p q => probTable lp z p q - G p q) ≤ ε)
    (hG' : ∀ s s' : ZMod 2, rmsMu n s s' G' ≤ 6) :
    (∀ s sB : ZMod 2,
      ∑ A : State n, ∑ X : State n, ∑ B : State n,
        mu n s A * mu n s X * mu n sB B *
          |(probTable lp z (A.1, X.1) (A.2, X.2) - G (A.1, X.1) (A.2, X.2)) *
            G' (X.1, B.1) (X.2, B.2)| ≤ 6 * ε) ∧
    (∀ sA s : ZMod 2,
      ∑ A : State n, ∑ X : State n, ∑ B : State n,
        mu n sA A * mu n s X * mu n s B *
          |G' (A.1, X.1) (A.2, X.2) *
            (probTable lp z (X.1, B.1) (X.2, B.2) - G (X.1, B.1) (X.2, B.2))| ≤ 6 * ε) ∧
    (∀ s : ZMod 2,
      ∑ A : State n, ∑ X : State n,
        mu n s A * mu n s X *
          |probTable lp z (A.1, X.1) (A.2, X.2) - G (A.1, X.1) (A.2, X.2)| ≤ ε) := by sorry

end LeakageRefresh.Continual
