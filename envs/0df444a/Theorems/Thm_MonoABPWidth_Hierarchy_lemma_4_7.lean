-- Prove2me | Theorems.Thm_MonoABPWidth_Hierarchy_lemma_4_7
-- name    : MonoABPWidth.Hierarchy.lemma_4_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-09T08:15:46.954238+00:00
-- url     : https://prove2.me/theorems/90f830b3-c6eb-47ee-8109-e902546a8c0a
-- title:
--   Lemma 4.7 — densification by a monotone projection
-- statement:
--   Let $k,n\ge1$, let $f$ be a real monotone polynomial supported inside $\operatorname{imm}_{k,n}$, and let $0<\alpha<1$. Suppose
--   $$
--   |\operatorname{supp}(f)|>\alpha|\operatorname{supp}(\operatorname{imm}_{k,n})|=\alpha k^{n-1}.
--   $$
--   For every positive divisor $m$ of $n$, there is a monotone projection $\pi$ to the variables of $\operatorname{imm}_{k,m}$ such that
--   $$
--   \operatorname{supp}(\pi(f))\subseteq\operatorname{supp}(\operatorname{imm}_{k,m}),\qquad
--   |\operatorname{supp}(\pi(f))|>\alpha^{m/n}|\operatorname{supp}(\operatorname{imm}_{k,m})|=\alpha^{m/n}k^{m-1}.
--   $$
--   Both density bounds are strict. This includes $k=1$, $m=1$, and $m=n$; substitutions may use arbitrary nonnegative constants and rename the boundary variables. It relates support density at different matrix-chain lengths.
--
--   Differences from the source:
--   - reading: matrix-chain length n ∈ ℕ, without an empty-chain convention → n ≥ 1 (and m ≥ 1 for divisors); reason: the paper specifies n matrices and k^(n−1) monomials (pp.4,10); an empty product and a depth-zero program would falsify the goal
--   - encoding: matrix entries and projection with boundary renaming → zero-based matrix entries and substitution between separate source and target variable types; reason: a finite relabelling preserves the IMM polynomial and allows the exact projections in the proof
-- source:
--   Julian Dörfler, Alexander Rogovskyy, A Width Hierarchy of Monotone Algebraic Branching Programs, STOC 2027 submission #927 (October 2026), Lemma 4.7, p. 10, PDF 11

import Definitions.Def_MonoABPWidth_Hierarchy_polynomials
import Definitions.Def_MonoABPWidth_Hierarchy_projection
import Definitions.Def_SetMultCost_imm

namespace MonoABPWidth.Hierarchy

/-- Lemma 4.7, p.10 / PDF11. The source and target variable types differ.
All positive divisors, including m=1 and m=n, and k=1 are retained. -/
theorem lemma_4_7 (k n : ℕ) (hk : 1 ≤ k) (hn : 0 < n)
    (f : MvPolynomial (SetMultCost.IMMVar k n) ℝ) (hf : MonotonePolynomial f)
    (hsub : f.support ⊆ (SetMultCost.imm ℝ k n).support)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hdense : α * ((SetMultCost.imm ℝ k n).support.card : ℝ) < (f.support.card : ℝ)) :
    ∀ m : ℕ, 0 < m → m ∣ n →
      ∃ π : MonotoneProjection (SetMultCost.IMMVar k n) (SetMultCost.IMMVar k m),
        (π.apply f).support ⊆ (SetMultCost.imm ℝ k m).support ∧
        Real.rpow α ((m : ℝ) / (n : ℝ)) *
          ((SetMultCost.imm ℝ k m).support.card : ℝ) < ((π.apply f).support.card : ℝ) := by sorry

end MonoABPWidth.Hierarchy
