-- Prove2me | Theorems.Thm_NearestDSM_lemma_3_2
-- name    : NearestDSM.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:20:08.830524+00:00
-- url     : https://prove2.me/theorems/5d5a9e10-b166-442d-8daf-0b4f933ad993
-- title:
--   Lemma 3.2 — linear description of an equivalence class (corrected: sign in item 2)
-- statement:
--   Let $\tilde y\in\mathbb R^{2n-1}$ and $\tilde x=(\hat x+A^T\tilde y)_+$. For $y\in\mathbb R^{2n-1}$ the following are equivalent:
--
--   1. $y\in[\tilde y]$;
--   2. for every entry $i$,
--   $$
--   (A^Ty)_i=(\tilde x-\hat x)_i\ \text{ if }\tilde x_i>0,\qquad (A^Ty)_i\le(\tilde x-\hat x)_i\ \text{ if }\tilde x_i=0;
--   $$
--   3. $\tilde x-\hat x-A^Ty\in(\mathbb R^{n^2}_+-\tilde x)^+$, where $(C-w)^+=\{v:(c-w)^Tv\ge 0\ \forall c\in C\}$ is the nonnegative polar cone of $C$ at $w$.
--
--   So every equivalence class is cut out by finitely many linear equations and inequalities in $y$.
--
--   **Formalization Note** Vectors in $\mathbb R^{n^2}$ are functions on (row, column) pairs.
--
--   Differences from the source:
--   - correction: item 2 printed as $(A^Ty)_i=(\hat x-\tilde x)_i$ if $\tilde x_i>0$ and $(A^Ty)_j\le(\hat x-\tilde x)_j$ if $\tilde x_j=0$ → $\tilde x-\hat x$ on both lines; reason: as printed the lemma is false; for the paper's $n=1$, $\hat X=[0]$, $A=[1]$, $\tilde y=y=1$ one has $\tilde x=1$ and $y\in[\tilde y]$ but $A^Ty=1\ne\hat x-\tilde x=-1$; the corrected sign agrees with item 3 and with the proof ($v_i=0$ for $\tilde x_i>0$, $v_i\ge0$ for $\tilde x_i=0$)
--   - encoding: size $n\ge1$ → `n + 1`, 0-based indices; reason: Lean convention, same instances
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, Lemma 3.2, pp.12-13

import Mathlib
import Definitions.Def_NearestDSM_Xmat
import Definitions.Def_NearestDSM_equivClass
open Matrix

namespace NearestDSM

/-- Hu, Im, Li & Wolkowicz, arXiv:2107.09631v1, Lemma 3.2, p.12–13 (corrected: sign in item 2). Let `ỹ ∈ ℝ^{2n−1}` and
`x̃ = (x̂ + Aᵀỹ)₊`. Then the following are equivalent:
1. `y ∈ [ỹ]`;
2. `(Aᵀy)_i = (x̃ − x̂)_i` if `x̃_i > 0`, and `(Aᵀy)_j ≤ (x̃ − x̂)_j` if `x̃_j = 0`;
3. `x̃ − x̂ − Aᵀy ∈ (ℝ^{n²}_+ − x̃)⁺`, the nonnegative polar cone
   `(C − w)⁺ = {v : (c − w)ᵀv ≥ 0, ∀ c ∈ C}` of `C = ℝ^{n²}_+` at `w = x̃` (p.12).

**Correction.** The page prints `(x̂ − x̃)` on both lines of item 2. That is false: for the paper's
`n = 1` and `X̂ = [0]` one has `A = [1]`; with `ỹ = y = 1`, `x̃ = 1` and `y ∈ [ỹ]`, but
`Aᵀy = 1 ≠ x̂ − x̃ = −1`. Item 3 and the proof ("`v_i = 0` for `x̃_i > 0` and `v_i ≥ 0` for
`x̃_i = 0`", `v = x̃ − x̂ − Aᵀy`) give `x̃ − x̂`, which is stated here.

**Formalization Note.** The paper's size `n` is `n + 1`; vectors in `ℝ^{n²}` are functions on
index pairs `(row, column)`. -/
theorem lemma_3_2 {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (yt y : Dual n) :
    List.TFAE
      [ y ∈ equivClass Xh yt,
        ∀ p : Fin (n + 1) × Fin (n + 1),
          (0 < Xmat Xh yt p.1 p.2 →
              ((Amat n)ᵀ *ᵥ WithLp.ofLp y) p = Xmat Xh yt p.1 p.2 - Xh p.1 p.2) ∧
            (Xmat Xh yt p.1 p.2 = 0 →
              ((Amat n)ᵀ *ᵥ WithLp.ofLp y) p ≤ Xmat Xh yt p.1 p.2 - Xh p.1 p.2),
        ∀ w : Fin (n + 1) × Fin (n + 1) → ℝ, 0 ≤ w →
          0 ≤ (w - fun p => Xmat Xh yt p.1 p.2) ⬝ᵥ
            ((fun p => Xmat Xh yt p.1 p.2 - Xh p.1 p.2) - (Amat n)ᵀ *ᵥ WithLp.ofLp y) ] := by sorry

end NearestDSM
