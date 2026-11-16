-- Prove2me | Theorems.Thm_L1Sparsifiers_Main_Supplement_theorem_3
-- name    : L1Sparsifiers.Main.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:16:43.559997+00:00
-- url     : https://prove2.me/theorems/b72f48ce-eade-41f6-b2dc-0651991cb368
-- title:
--   Theorem 3 — every $n$-dimensional subspace of $\ell_1$ is $(1+\varepsilon)$-close to a subspace of $\ell_1^N$, $N=O(n/\varepsilon^2)$
-- statement:
--   Let $\ell_1$ be the real Banach space of sequences $(x_k)_{k\in\mathbb N}$ with $\|x\|_1=\sum_k|x_k|<\infty$, and let $\ell_1^N=(\mathbb R^N,\|\cdot\|_1)$. There is an absolute constant $C>0$ such that for every $0<\varepsilon\le1$ and every $n$-dimensional linear subspace $X\subseteq\ell_1$ there are $N\le C\,n/\varepsilon^2$ and an $n$-dimensional linear subspace $Y\subseteq\ell_1^N$ with
--   $$d_{BM}(X,Y)\le1+\varepsilon ,$$
--   where $X$ and $Y$ carry the restricted $\ell_1$ norms and $d_{BM}$ is the Banach–Mazur distance.
--
--   This answers Schechtman's 1986 question on the number of coordinates needed to $(1+\varepsilon)$-embed $n$-dimensional subspaces of $L_1$ into $\ell_1^N$, improving Talagrand's $O(n\log n/\varepsilon^2)$.
--
--   **Formalization Note** $\ell_1$ is `lp (fun _ : ℕ => ℝ) 1`, $\ell_1^N$ is `PiLp 1 (fun _ : Fin N => ℝ)`, and $d_{BM}$ is the supplement definition `banachMazur`, an infimum in $[0,\infty]$ over all isomorphisms.
--
--   Differences from the source:
--   - encoding: d_BM(X, Y) ≤ 1 + ε → banachMazur X Y ≤ ENNReal.ofReal (1 + ε), the infimum of ‖T‖‖T⁻¹‖ over all T : X ≃L[ℝ] Y in [0, ∞]; reason: the same infimum; it is +∞ only when no isomorphism exists, and for n = 0 it is 0 instead of the conventional 1, which is ≤ 1 + ε either way
--   - encoding: ℓ1 and ℓ1^N = (ℝ^N, ‖·‖₁) → lp (fun _ : ℕ => ℝ) 1 and PiLp 1 (fun _ : Fin N => ℝ); subspaces are Submodules; X n-dimensional is FiniteDimensional ℝ X with finrank n, Y has finrank n; reason: the same Banach spaces and subspaces (finrank alone is 0 on an infinite-dimensional subspace, so finite dimensionality of X is stated); finite-dimensional subspaces are automatically closed
--   - encoding: N ≤ O(n/ε²) → N ≤ C·n/ε² for one C > 0 chosen before n, ε, X; reason: O(·) with an absolute constant means one uniform C
-- source:
--   Victor Reis, Thomas Rothvoss, Linear-size ℓ1 sparsifiers, STOC 2027 submission #162 (October 2026; PDF SHA-256 5137e7dee3cd303bd508f90f5f42c955632af5dc2ec978d9ef575bae4ce23710), §1.1, Theorem 3, pp.3–4 (ℓ1, ℓ1^N defined on p.3)

import Mathlib
import Definitions.Def_L1Sparsifiers_Main_Supplement_BanachMazur

namespace L1Sparsifiers.Main.Supplement

open scoped ENNReal

/-- **Theorem 3** (Reis–Rothvoss, STOC 2027 submission #162, p.4).
"Let 0 < ε ≤ 1 and let X be an n-dimensional subspace of ℓ1. Then there exists an n-dimensional
subspace Y of ℓ1^N with N ≤ O(n/ε²) so that d_BM(X, Y) ≤ 1 + ε."

`ℓ1` is the infinite-dimensional real Banach space of sequences `(x_k)_{k∈ℕ}` with `‖x‖₁ < ∞`
(`lp (fun _ : ℕ => ℝ) 1`), and `ℓ1^N = (ℝ^N, ‖·‖₁)` (`PiLp 1 (fun _ : Fin N => ℝ)`). Subspaces carry
the restricted norm. "`n`-dimensional" is `FiniteDimensional ℝ X` together with
`Module.finrank ℝ X = n` (`finrank` alone is `0` on an infinite-dimensional subspace). `d_BM` is the Banach–Mazur distance `banachMazur`, an infimum over all
isomorphisms. The `O(n/ε²)` is one absolute constant `C > 0`, chosen before `n, ε, X`. -/
theorem theorem_3 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
        ∀ X : Submodule ℝ (lp (fun _ : ℕ => ℝ) 1), FiniteDimensional ℝ X → Module.finrank ℝ X = n →
          ∃ (N : ℕ) (Y : Submodule ℝ (PiLp 1 (fun _ : Fin N => ℝ))),
            (N : ℝ) ≤ C * n / ε ^ 2 ∧ Module.finrank ℝ Y = n ∧
            banachMazur X Y ≤ ENNReal.ofReal (1 + ε) := by sorry

end L1Sparsifiers.Main.Supplement
