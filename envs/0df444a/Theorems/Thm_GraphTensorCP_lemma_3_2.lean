-- Prove2me | Theorems.Thm_GraphTensorCP_lemma_3_2
-- name    : GraphTensorCP.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:04:56.647063+00:00
-- url     : https://prove2.me/theorems/034380f7-d6d7-4339-a4b1-3a5eb3b9e94d
-- title:
--   Lemma 3.2 — $\tilde R_{\mathbb F}(\mathcal C_n(a))=1+\sum_j(a_j-1)$, $\mathcal C_n(a)\trianglelefteq I_n(D)$, and rank $D$ over large fields
-- statement:
--   For every field $\mathbb F$, every integer $n\ge2$ and all positive integers $a_1,\dots,a_{n-1}$, with $D=1+\sum_{j=1}^{n-1}(a_j-1)$:
--
--   1. $$\tilde R_{\mathbb F}\big(\mathcal C_n(a_1,\dots,a_{n-1})\big)=D;$$
--   2. $\mathcal C_n(a_1,\dots,a_{n-1})\trianglelefteq I_n(D)$, i.e. the diagonal tensor $I_n(D)$ degenerates to $\mathcal C_n(a_1,\dots,a_{n-1})$;
--   3. if $\mathbb F$ contains at least $D$ distinct elements, the ordinary rank $R_{\mathbb F}(\mathcal C_n(a_1,\dots,a_{n-1}))$ also equals $D$.
--
--   The degeneration holds over every field, including small finite fields, through rational interpolation; it is the resource behind the separation theorem.
--
--   **Formalization Note** Degeneration is the published `MME.Degenerates` (polynomial local maps whose leading coefficient is the target, Definition 2.15). "At least $D$ distinct elements" is $D\le|\mathbb F|$ as cardinals.
--
--   Differences from the source:
--   - encoding: $\tilde R_{\mathbb F}(T)=\lim_N R_{\mathbb F}(T^{\otimes N})^{1/N}$ → `MME.tensorAsymptoticRank` $=\inf_{N\ge1}R(T^{\otimes N})^{1/N}$; reason: the paper proves the limit equals this infimum (p.19); both are $0$ at $T=0$
--   - encoding: $\mathbb F$ contains at least $D$ distinct elements → $D\le\#\mathbb F$ (`Cardinal.mk K`); reason: same condition
--   - encoding: $a_1,\dots,a_{n-1}$ → $a:\mathrm{Fin}(n-1)\to\mathbb N$ with $a_j>0$, $a_j-1$ as natural subtraction; reason: relabeling; the subtraction is exact since $a_j\ge1$
-- source:
--   H. Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Lemma 3.2, p.29

import Mathlib
import Definitions.Def_GraphTensorCP_polyMulTensor
import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_degeneration

universe u

namespace GraphTensorCP

/-- **Lemma 3.2** (asymptotic rank of polynomial multiplication), Zhou, *Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), p.29:
"For every field F, every integer n ≥ 2, and all positive integers a₁, . . . , a_{n−1},
R̃_F(C_n(a₁, . . . , a_{n−1})) = 1 + Σ_{j=1}^{n−1}(a_j − 1). Moreover, C_n(a₁, . . . , a_{n−1}) ⊴ I_n(D), where
D = 1 + Σ_{j=1}^{n−1}(a_j − 1). If F contains at least D distinct elements, then the ordinary rank also
equals D."

**Formalization Note.** `⊴` is the published `MME.Degenerates X Y` ("`X` degenerates from `Y`",
Definition 2.15), with `X = C_n(a)` and `Y = I_n(D) = MME.TensorObj.diagObj K n D`. The ordinary rank is
`MME.tensorRankObj`. "F contains at least D distinct elements" is `D ≤ #F` as cardinals. `a_j − 1` is
natural-number subtraction, exact because every `a_j ≥ 1`. -/
theorem lemma_3_2 {K : Type u} [Field K] {n : ℕ} (hn : 1 < n) (a : Fin (n - 1) → ℕ)
    (ha : ∀ j, 0 < a j) :
    MME.tensorAsymptoticRank (polyMulTensor K n a) = ((1 + ∑ j, (a j - 1) : ℕ) : ℝ) ∧
    MME.Degenerates (polyMulTensor K n a) (MME.TensorObj.diagObj K n (1 + ∑ j, (a j - 1))) ∧
    (((1 + ∑ j, (a j - 1) : ℕ) : Cardinal.{u}) ≤ Cardinal.mk K →
      MME.tensorRankObj (polyMulTensor K n a) = 1 + ∑ j, (a j - 1)) := by sorry

end GraphTensorCP
