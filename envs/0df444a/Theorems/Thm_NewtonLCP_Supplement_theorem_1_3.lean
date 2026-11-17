-- Prove2me | Theorems.Thm_NewtonLCP_Supplement_theorem_1_3
-- name    : NewtonLCP.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:17:07.028836+00:00
-- url     : https://prove2.me/theorems/c43dc65b-ce41-404e-ae99-6f34a8dcb98b
-- title:
--   Theorem 1.3 — recognizing any class between $P$ and $P_0$ is coNP-hard; recognizing $P_\star$ is coNP-complete
-- statement:
--   Let $P$ be the class of P-matrices (all principal minors positive), $P_0$ the class of matrices whose principal minors are all nonnegative, and $P_\star$ the class of matrices of finite handicap $\hat\kappa$. Then:
--
--   1. For any matrix class $\tilde P$ with $P\subseteq\tilde P\subseteq P_0$, deciding whether a given $M\in\mathbb Q^{n\times n}$ belongs to $\tilde P$ is coNP-hard.
--   2. Deciding whether a given $M\in\mathbb Q^{n\times n}$ belongs to $P_\star$ is coNP-complete.
--
--   The theorem settles the complexity of recognizing sufficient matrices, and shows that no class sandwiched between $P$ and $P_0$ can be recognized in polynomial time unless coNP $=$ P.
--
--   **Formalization Note** A matrix class is any family $\tilde P_n\subseteq\mathbb Q^{n\times n}$ (no decidability assumed), with $P\subseteq\tilde P\subseteq P_0$ read through the real cast. The decision problem is the language of binary codes of the class; coNP-hardness is with respect to polynomial-time many-one reductions on Cook's one-tape Turing machines (published `CookPvsNP_defs`). The cited results [Cox94] and [Tse00] used in the proof are not hypotheses.
--
--   Differences from the source:
--   - encoding: "deciding if $M\in\mathbb Q^{n\times n}$ is in $\tilde P$" → the language of the binary codes `encMat M` of the matrices of $\tilde P$, with coNP, reductions and Turing machines from `CookPvsNP_defs`; reason: the paper names no input encoding or machine model; the encoding is injective and of size polynomial in the paper's length(M).
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Theorem 1.3, p.4 (proof §7.1, pp.24–26)

import Mathlib
import Definitions.Def_NewtonLCP_MatrixClasses
import Definitions.Def_NewtonLCP_Handicap
import Definitions.Def_PriceRobust_Stability_ZPMatrix
import Definitions.Def_NewtonLCP_Supplement_Complexity

namespace NewtonLCP.Supplement

/-- **Theorem 1.3** (hardness of recognizing classes between `P` and `P₀`). Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Theorem 1.3, p.4
(proof §7.1, pp.24–26).

For any matrix class `P̃` such that `P ⊆ P̃ ⊆ P₀`, deciding if `M ∈ ℚⁿˣⁿ` is in `P̃` is
coNP-hard. In particular, deciding if `M ∈ ℚⁿˣⁿ` is in `P⋆` is coNP-complete.

**Formalization Note.**
* A matrix class is a family `P̃ₙ ⊆ ℚⁿˣⁿ`, `n ≥ 0`, with no decidability or other condition;
  `P ⊆ P̃ ⊆ P₀` is read on rational matrices through the real cast (`P` the published
  `PriceRobust.Stability.IsPMatrix`, `P₀` the published `IsP0`, `P⋆` the published `IsPStar`).
* The decision problem is the language `matLang P̃` of binary codes `encMat M` of the matrices of
  the class (an injective encoding of size polynomial in `n² + length(M)`).
* coNP, polynomial-time reductions, coNP-hard and coNP-complete are those of
  `NewtonLCP.Supplement.Complexity`, built on the published `CookPvsNP_defs`.
* Both conclusions are stated: (a) for every such `P̃`; (b) for `P̃ = P⋆`, membership in coNP and
  coNP-hardness. The results the proof cites ([Cox94], [Tse00]) are not hypotheses. -/
theorem theorem_1_3 :
    (∀ Pt : (n : ℕ) → Set (Matrix (Fin n) (Fin n) ℚ),
      (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ),
        PriceRobust.Stability.IsPMatrix (M.map ((↑) : ℚ → ℝ)) → M ∈ Pt n) →
      (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ), M ∈ Pt n → IsP0 (M.map ((↑) : ℚ → ℝ))) →
      CoNPHard (matLang Pt)) ∧
    CoNPComplete (matLang (fun n => {M : Matrix (Fin n) (Fin n) ℚ |
      IsPStar (M.map ((↑) : ℚ → ℝ))})) := by sorry

end NewtonLCP.Supplement
