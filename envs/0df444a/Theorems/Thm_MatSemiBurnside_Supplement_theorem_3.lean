-- Prove2me | Theorems.Thm_MatSemiBurnside_Supplement_theorem_3
-- name    : MatSemiBurnside.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:46:59.713196+00:00
-- url     : https://prove2.me/theorems/858cfc1c-2098-4d48-b8c0-85cb7cef2419
-- title:
--   Theorem 3: bounded groups in $\overline{\langle X\rangle}$ give a finite $\langle X\rangle/\sim$ of diameter $\le 2^{2d(d+3)}N^d$
-- statement:
--   Let $d$ be a positive integer, $X\subseteq\mathrm{Mat}_d(\mathbb Q)$ finite, and let $\overline{\langle X\rangle}$ be the Zariski closure of $\langle X\rangle$ in $\mathrm{Mat}_d(\overline{\mathbb Q})$. Let $\sim$ be a congruence on $\overline{\langle X\rangle}$. Assume there is $N\ge1$ such that
--   $$|G/\sim|\le N\quad\text{for every group } G\le\overline{\langle X\rangle},$$
--   where a group $G\le\overline{\langle X\rangle}$ is a subset that is a group under matrix multiplication (with its own identity, an idempotent) and $|G/\sim|$ counts the classes of $\overline{\langle X\rangle}/\sim$ meeting $G$. Then the quotient $\langle X\rangle/\sim$ of $\langle X\rangle$ by the restriction of $\sim$ is finite, and its diameter is at most
--   $$2^{2d(d+3)}N^d:$$
--   every $a\in\langle X\rangle$ satisfies $a\sim a_1\cdots a_k$ with $a_1,\dots,a_k\in X$ and $1\le k\le 2^{2d(d+3)}N^d$.
--
--   The bound is singly exponential in $d$ and does not depend on $|X|$. This is the finiteness criterion applied in the border-complexity separations of the paper, where every group in the closure lies in one class.
--
--   **Formalization Note** $\overline{\mathbb Q}$ is `AlgebraicClosure ℚ`; the closure is `closureSG X`; groups are `IsGroupIn`; $\langle X\rangle/\sim$ is the set `quotImage X c` of classes meeting $\langle X\rangle$, and the diameter clause is `DiameterLEBar`.
--
--   Differences from the source:
--   - generalization: X finite and nonempty (standing assumption of §3, p.7) → any finite X, the empty set included; reason: for X = ∅ the closure is empty, the quotient is empty and finite, and the diameter clause is vacuous; the statement specializes to nonempty X
--   - encoding: "Assume that there exists N ≥ 1 such that … Then …" → for every N ≥ 1 satisfying the bound, the conclusion; reason: logically equivalent (the conclusion's bound uses that N)
--   - encoding: ⟨X⟩/∼, |G/∼|, "diameter at most" → the set of classes of ⟨X⟩‾/∼ meeting the embedded ⟨X⟩; `Set.encard` of the classes met by G; every element of ⟨X⟩ congruent to a word over X of length between 1 and the bound (`DiameterLEBar`); reason: the classes of the restriction of ∼ to ⟨X⟩ correspond bijectively to the classes of ⟨X⟩‾/∼ meeting ⟨X⟩; same values
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), Theorem 3, p.4 (restated identically pp.13 and 39; proof Appendix E, pp.35–40)

import Mathlib
import Definitions.Def_MatSemiBurnside_Supplement_closureSG
import Definitions.Def_MatSemiBurnside_Supplement_IsGroupIn
import Definitions.Def_MatSemiBurnside_Supplement_classesMeetingBar
set_option autoImplicit false

namespace MatSemiBurnside.Supplement

/-- **Theorem 3.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), Theorem 3, p.4 (restated identically pp.13 and 39; proof App. E, pp.35–40):
"Let X ⊆ Mat_d(ℚ) be finite and ∼ be a congruence on ⟨X⟩‾. Assume that there exists N ≥ 1 such that
|G/∼| ≤ N for every group G ≤ ⟨X⟩‾. Then ⟨X⟩/∼ is finite and has diameter at most 2^{2d(d+3)} N^d."

**Formalization Note.**
* ⟨X⟩‾ = `closureSG X` is the Zariski closure in Mat_d(ℚ̄) of ⟨X⟩ embedded entrywise (p.13), ℚ̄ =
  `AlgebraicClosure ℚ`; ∼ is any congruence `c` on it.
* G ranges over all subsets of ⟨X⟩‾ that are groups under matrix multiplication with their own identity
  (`IsGroupIn`); |G/∼| is the `Set.encard` of the classes of ⟨X⟩‾/∼ meeting G.
* ⟨X⟩/∼ (the quotient of ⟨X⟩ by the restriction of ∼) is finite: the set `quotImage X c` of classes meeting
  ⟨X⟩ is finite. Its diameter is at most 2^{2d(d+3)} N^d (`DiameterLEBar`: lengths with respect to X).
* "there exists N ≥ 1 such that … Then …" is stated as: for every N ≥ 1 satisfying the bound. -/
theorem theorem_3 {d : ℕ} (hd : 0 < d) (X : Finset (Matrix (Fin d) (Fin d) ℚ)) (c : Con (closureSG X)) (N : ℕ) (hN : 1 ≤ N) (hG : ∀ G : Set (Matrix (Fin d) (Fin d) Qbar), IsGroupIn (closureSG X : Set (Matrix (Fin d) (Fin d) Qbar)) G → (classesMeetingBar c G).encard ≤ (N : ℕ∞)) :
    (quotImage X c).Finite ∧ DiameterLEBar X c (2 ^ (2 * d * (d + 3)) * N ^ d) := by sorry

end MatSemiBurnside.Supplement
