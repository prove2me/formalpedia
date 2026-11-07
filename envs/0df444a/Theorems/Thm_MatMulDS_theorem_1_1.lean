-- Prove2me | Theorems.Thm_MatMulDS_theorem_1_1
-- name    : MatMulDS.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:09:07.920656+00:00
-- url     : https://prove2.me/theorems/c993f044-cbcc-4c53-a20b-fd02f2f0ff84
-- title:
--   Theorem 1.1 — subquadratic preprocessing and sublinear queries below $\alpha$, and past $\alpha$ under slope zero
-- statement:
--   Let $\mathbb F$ be a field of characteristic zero and $\alpha$ its dual exponent.
--
--   For every constant $0<\alpha'<\alpha$ there is a constant $\beta>0$ with the following property. Let $N,D\ge1$ be integers with $D\le N^{\alpha'}$, and let $A,B$ be $N\times D$ and $D\times N$ matrices over $\mathbb F$. Then we can preprocess $A$ and $B$ in $O(N^{2-\beta})$ time such that upon any query $(I,J)\in[N]^2$ we can compute $(AB)[I,J]$ in $O(N^{\alpha'-\beta})$ time. In particular, any $N^{2-\alpha'}$ entries of $AB$ can be computed in $O(N^{2-\beta})$ time.
--
--   Moreover, if
--   $$\omega(1,\alpha+x,1)\le2+o(x)\quad\text{as }x\to0^+,$$
--   then there are constants $\delta,\gamma>0$ such that for all integers $N,D\ge1$ with $D\le N^{\alpha+\delta}$, we can preprocess $A$ and $B$ in $O(N^{2-\gamma})$ time such that upon any query $(I,J)$ we can compute $(AB)[I,J]$ in $O(N^{\alpha-\gamma})$ time.
--
--   All data structures are deterministic and allow adaptive queries. This is the main theorem of the source, and it gives nontrivial structures at inner dimensions where no almost-quadratic offline algorithm is known.
--
--   **Formalization Note** One program on the published algebraic RAM, with its constants, is fixed before $N$ and $D$, and all machine steps are counted.
--
--   Differences from the source:
--   - generalization: "preprocess in $O(N^{2-\beta})$ time" → the stored cells are also at most $CN^{2-\beta}$; reason: the space clause of Theorem 7.3, p.46; it implies the printed statement
--   - generalization: a program with a word size → one program for every word size $w\ge K\lceil\log_2(N+1)\rceil+K$; reason: it specializes to each word size above the threshold and cannot exploit a huge word
--   - encoding: "a field of characteristic zero" → $F:\mathrm{Type}$ with decidable equality, fixed first, and $\beta$ after it; reason: the published machine requires this; $\alpha$ depends on $\mathbb F$
--   - encoding: fixed constants of the algorithm → a list $c$ of constants of $\mathbb F$ in the input field memory, chosen with the program, before $N,D$; reason: the machine's only field literals are $0$ and $1$, and rectangular schemes may use other constants
--   - encoding: input and query → words $N,D$; field cells $c,A,B$ in row-major order; words $I,J$ 0-based; answer in field cell $0$; reason: a layout on the machine; the machine's $\texttt{fcoin}$ is excluded for "deterministic"
--   - encoding: $\alpha$ of the second part → the hypothesis $0<\alpha$; reason: true by [Cop82] (p.14), so it excludes no field; without it $O(N^{\alpha-\gamma})$ could not bound a positive step count
--   - encoding: (1.2), $o(x)$ → $\forall\varepsilon>0\,\exists x_0>0\,\forall x\in(0,x_0),\ \omega(1,\alpha+x,1)\le2+\varepsilon x$; reason: the meaning of $o(x)$ as $x\to0^+$
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Theorem 1.1, pp.3–4 (PDF pp.5–6)

import Mathlib
import Definitions.Def_MatMulDS_omegaExp
import Definitions.Def_MatMulDS_IsMatMulOracle

set_option autoImplicit false

open MatroidSensOracle

namespace MatMulDS

/-- **Theorem 1.1, pp.3–4** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held file sha256 6c5a1c16…). Let `F` be a field of characteristic zero and `α` its dual exponent.

For every constant `0 < α′ < α`, there is a constant `β > 0` with the following property. Let `N, D ≥ 1` be integers with `D ≤ N^{α′}`, and let `A`, `B` be `N × D` and `D × N` matrices over `F`. Then we can preprocess `A` and `B` in
`O(N^{2−β})` time, such that upon any query `(I, J) ∈ [N]²` we can compute `(AB)[I, J]` in `O(N^{α′−β})` time. In particular, any `N^{2−α′}` entries of `AB` can be computed in `O(N^{2−β})` time.

Moreover, if `ω(1, α + x, 1) ≤ 2 + o(x)` as `x → 0⁺`, (1.2), then there are constants `δ, γ > 0` such that for all integers `N, D ≥ 1` with `D ≤ N^{α+δ}`, we can preprocess `A` and `B` as above in `O(N^{2−γ})` time, such that upon any
query `(I, J) ∈ [N]²` we can compute `(AB)[I, J]` in `O(N^{α−γ})` time.

**Formalization Note.**
* Machine: one coin-free program on the published `MatroidSensOracle_AlgRAM`, in `IsMatMulOracle`; it is fixed before `N` and `D` along with the list `c` of constants of `F`, the word-size constant `K` and the constant `C`.
* `F` comes first, since `α` depends on it; `β` then depends on `F` and `α′`.
* Each step of the machine counts, so the bounds include constructing whatever circuits the program uses, and "stored cells at most `C N^{2−β}`" is included (the space clause of Theorem 7.3).
* (1.2) is written with `ε` and `x₀`. `0 < α` in the second part is true by [Cop82] (p.14), and the conclusion's `O(N^{α−γ})` could not hold for a positive step count without it.
* The "In particular" clause holds for every list of at most `N^{2−α′}` queries; see `AnswersListWithin` for adaptive choices. -/
theorem theorem_1_1 (F : Type) [Field F] [CharZero F] [DecidableEq F] :
    (∀ α' : ℝ, 0 < α' → α' < dualExponent F →
      ∃ β : ℝ, 0 < β ∧ ∃ (O : AOracle) (c : List F) (K : ℕ) (C : ℝ), 0 < C ∧
        IsMatMulOracle O c K (fun N D => (D : ℝ) ≤ (N : ℝ) ^ α')
          (fun N _ => C * (N : ℝ) ^ (2 - β)) (fun N _ => C * (N : ℝ) ^ (α' - β)) ∧
        ∀ N D : ℕ, 1 ≤ N → 1 ≤ D → (D : ℝ) ≤ (N : ℝ) ^ α' →
        ∀ (A : Matrix (Fin N) (Fin D) F) (B : Matrix (Fin D) (Fin N) F) (w : ℕ),
          K * Nat.clog 2 (N + 1) + K ≤ w →
          ∀ qs : List (Fin N × Fin N), (qs.length : ℝ) ≤ (N : ℝ) ^ (2 - α') →
            AnswersListWithin O c w A B qs (C * (N : ℝ) ^ (2 - β))) ∧
    (0 < dualExponent F →
      (∀ ε : ℝ, 0 < ε → ∃ x₀ : ℝ, 0 < x₀ ∧ ∀ x : ℝ, 0 < x → x < x₀ →
        omegaExp F 1 (dualExponent F + x) 1 ≤ 2 + ε * x) →
      ∃ δ γ : ℝ, 0 < δ ∧ 0 < γ ∧ ∃ (O : AOracle) (c : List F) (K : ℕ) (C : ℝ), 0 < C ∧
        IsMatMulOracle O c K (fun N D => (D : ℝ) ≤ (N : ℝ) ^ (dualExponent F + δ))
          (fun N _ => C * (N : ℝ) ^ (2 - γ)) (fun N _ => C * (N : ℝ) ^ (dualExponent F - γ))) := by sorry

end MatMulDS
