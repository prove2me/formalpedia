-- Prove2me | Theorems.Thm_OAI_Erdos3_PositiveShiftBasis_exists_factored_positive_shift_contradiction_s2
-- name    : OAI.Erdos3.PositiveShiftBasis.exists_factored_positive_shift_contradiction_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:56:21.736581+00:00
-- url     : https://prove2.me/theorems/be7d421d-630a-462b-86fd-f74a11b0ad3e
-- title:
--   A cyclic shift comparison at degree s+1 yields the factored positive-shift contradiction for some exponent
-- statement:
--   Let $s$ and $c$ be natural numbers with $c \ge 2$, and let $\varepsilon$ be a real number with $0 < \varepsilon < 1$. Assume `CyclicShiftComparison (s + 1) (ε / 2) c` (at universe level $0$), a property defined by OpenAI meaning: for every natural number $N \ge 1$ and real $p \ge 2$ with $N$ odd and $e^{(p+2)^c} \le N$, and all $f, g, J : \mathbb{Z}/N\mathbb{Z} \to \mathbb{R}$ with values in $[0, e^{p}]$, if `CyclicNiltestUpperComparison (s + 1) N ((p + 2)^c) (exp (-(p + 2)^c)) f g` holds (OpenAI's property: for every niltest of degree at most $s+1$, with values in $[0,1]$ and complexity at most $(p+2)^c$, the average over $x \in \mathbb{Z}/N\mathbb{Z}$ of $(f(x) - g(x))$ times the real part of its cyclic evaluation at $x$ is at most $e^{-(p+2)^c}$), then there is a set $E \subseteq \mathbb{Z}/N\mathbb{Z}$ with $|E| \le e^{-p} N$ such that `CyclicNiltestShiftBound s N p (exp (-p)) (fun n => f n - (1 + ε/2) * g n) J E` holds (OpenAI's property: for every shift $h \notin E$ and every niltest $T$ of degree at most $s$ with values in $[0,1]$ and complexity at most $p$, $\mathbb{E}_{x}\,(f(x) - (1+\varepsilon/2) g(x))\,J(x+h)\,\operatorname{Re} T_N(x) \le e^{-p}$). Here $(s+1) - 1 = s$.
--
--   Then there is a natural number $D_{\exp} \ge 2$ such that `FactoredPositiveShiftContradictionSpec s Dexp ε` holds. This is a proposition defined by OpenAI. It says: for every $N \ge 1$, every real $q$, all $f_1, f_2, \mathrm{weight} : \mathbb{Z}/N\mathbb{Z} \to \mathbb{R}$, every positive-shift basis $B$ (OpenAI's structure `PositiveShiftBasis (s + 1) N q (fun n => f₁ n - (1 + ε) * f₂ n) weight`, recording a rational filtered nilmanifold of degree $s+1$ and geometric complexity at most $q$, a large set of shifts, and for each shift a family of niltest modes with frequencies of bounded height that correlate with $n \mapsto (f_1(n) - (1+\varepsilon) f_2(n))\,\mathrm{weight}(n+h)$), every family of rational filtered nilmanifolds $D_j$ of degree $s+1$ and $E_j$ of degree $s+2$ indexed by $j < $ `B.count`, square-model data $Y_j$ for $E_j$, niltests $A_j$ and $R(h)_j$, an anchor, a shift set $H$, a real $p$ and common factorization data `F : B.CommonFactorization D (fun j => (Y j).quotientModel) A R anchor H p` (OpenAI's structure) — if $H \subseteq$ `B.shifts`, $2 \le p$, $q \le p$, all of $D_j$, $E_j$, the full and quotient models of $Y_j$ have geometric complexity at most $p$, the coordinates of the basis of $Y_j$ in the basis of $E_j$ have rational log-height at most $p$, and there are polynomial orbits $g_0$, branch choices, real group elements $\eta, \gamma$ and square orbits $r_{\mathrm{Sq}}$ satisfying the lattice, coordinate-size ($\le e^{p}$) and orbit-factorization identities written in the definition for every shift of `F.shifts`, and if $N$ is odd, $e^{(\beta(p) + 2)^{D_{\exp}}} \le N$ where $\beta(p) = $ `productExpansionBudget p` $= (2p+4)^2 + p + 2$, and $f_1, f_2, \mathrm{weight}$ take values in $[0, e^{p}]$ — then `CyclicNiltestUpperComparison (s + 2) N ((β(p) + 2)^Dexp) (exp (-(β(p) + 2)^Dexp)) f₁ f₂` (at universe level $0$) is false.
--
--   Lean: `OAI.Erdos3.PositiveShiftBasis.exists_factored_positive_shift_contradiction_s2`, which states OpenAI's `OAI.Erdos3.PositiveShiftBasis.exists_factored_positive_shift_contradiction` (in `lean/OAI/Combinatorics/Progressions/Estimates/FactoredPositiveShiftContradiction.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B230` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/FactoredPositiveShiftContradiction.lean (declaration OAI.Erdos3.PositiveShiftBasis.exists_factored_positive_shift_contradiction)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B230

section

namespace OAI

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

theorem exists_factored_positive_shift_contradiction_s2 (s c : ℕ) (hc : 2 ≤ c)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hshift : CyclicShiftComparison.{0} (s + 1) (epsilon / 2) c) :
    ∃ Dexp : ℕ, 2 ≤ Dexp ∧ FactoredPositiveShiftContradictionSpec s Dexp epsilon := by
  sorry

end Erdos3.PositiveShiftBasis

end OAI
end
