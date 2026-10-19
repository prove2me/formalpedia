-- Prove2me | Theorems.Thm_OAI_Erdos3_CyclicBohr_Set_small_sum_average_of_exponential_niltest_comparison_s2
-- name    : OAI.Erdos3.CyclicBohr.Set.small_sum_average_of_exponential_niltest_comparison_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:47:12.729882+00:00
-- url     : https://prove2.me/theorems/8bae772e-28ee-424d-bc37-36760e11ae32
-- title:
--   A degree-1 niltest upper comparison makes the double Bohr-set average of f - g exponentially small
-- statement:
--   Let $N \ge 1$ be a natural number. Let $B$ be a Bohr set in $\mathbb{Z}/N\mathbb{Z}$ in the sense of OpenAI's structure `CyclicBohr.Set N`: a finite set of frequencies $\Gamma \subseteq \mathbb{Z}/N\mathbb{Z}$ together with a radius $\rho = $ `B.radius` $\ge 0$; its carrier `B.carrier` is the set of $x \in \mathbb{Z}/N\mathbb{Z}$ with $\|1 - \chi_r(x)\| \le \rho$ for every $r \in \Gamma$, where $\chi_r$ is the additive character `character r` of $\mathbb{Z}/N\mathbb{Z}$, and its rank `B.rank` is $|\Gamma|$. Assume that $B$ is rank-regular (`B.IsRankRegular`, defined by OpenAI: with $d = 2\max(\texttt{B.rank}, 1)$, for every $\kappa \in \mathbb{R}_{\ge 0}$ with $\kappa \le 1/(100 d)$ one has $(1 - 100 d \kappa)\,|B| \le |B_{1-\kappa}|$ and $|B_{1+\kappa}| \le (1 + 100 d\kappa)\,|B|$, where $B_t$ is $B$ with radius multiplied by $t$ and $|\cdot|$ is the size of the carrier) and that $\rho \le 1$.
--
--   Let $f, g : \mathbb{Z}/N\mathbb{Z} \to \mathbb{R}$, and let $W, A, E, R, P$ be real numbers with $W \ge 0$, $A \ge 0$, $E \ge 0$, $R \ge 0$, $W \le e^{A}$ and $e^{-R} \le \rho$. Assume $f(x) \ge 0$ and $g(x) \le W$ for all $x$, and
--   $$2\,\texttt{B.rank} + A + E + R + 1612 \le P, \qquad E + 2 + \texttt{B.rank}\,(R + 10) \le P.$$
--   Assume `CyclicNiltestUpperComparison 1 N P (exp (-P)) f g` (at universe level $0$), a property defined by OpenAI meaning: for every rational filtered nilmanifold $D$ (OpenAI's `RationalFilteredNilmanifold L s dim`, with $L$ a Lie algebra over $\mathbb{Q}$ in universe $0$ and with the standard topological instances on $\mathbb{R} \otimes_{\mathbb{Q}} L$) of degree $s \le 1$, and every one-variable niltest $T$ on $D$ (OpenAI's `D.Niltest`) whose observable takes values in $[0,1]$ (`T.UnitIntervalValued`) and whose complexity is at most $P$ (`T.ComplexityLE P`),
--   $$\mathbb{E}_{x \in \mathbb{Z}/N\mathbb{Z}}\, (f(x) - g(x))\,\operatorname{Re} T_N(x) \le e^{-P},$$
--   where $T_N(x)$ is the cyclic evaluation `T.evalCyclic N (fun _ => x)`.
--
--   Then for every $z \in \mathbb{Z}/N\mathbb{Z}$,
--   $$\mathbb{E}_{s \in \texttt{B.carrier}}\ \mathbb{E}_{t \in \texttt{B.carrier}}\ \bigl(f(z + s + t) - g(z + s + t)\bigr) \le e^{-E}.$$
--
--   Lean: `OAI.Erdos3.CyclicBohr.Set.small_sum_average_of_exponential_niltest_comparison_s2`, which states OpenAI's `OAI.Erdos3.CyclicBohr.Set.small_sum_average_of_exponential_niltest_comparison` (in `lean/OAI/Combinatorics/Progressions/Fourier/BohrNiltestBudget.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B130` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Fourier/BohrNiltestBudget.lean (declaration OAI.Erdos3.CyclicBohr.Set.small_sum_average_of_exponential_niltest_comparison)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B130

section

namespace OAI

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem small_sum_average_of_exponential_niltest_comparison_s2
    (B : Set N) (hB : B.IsRankRegular) (hB1 : B.radius ≤ 1)
    (f g : ZMod N → ℝ) {W A E R P : ℝ}
    (hW : 0 ≤ W) (hA : 0 ≤ A) (hE : 0 ≤ E) (hR : 0 ≤ R)
    (hWcap : W ≤ Real.exp A) (hwidth : Real.exp (-R) ≤ B.radius)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ W)
    (hcomplexity : 2 * (B.rank : ℝ) + A + E + R + 1612 ≤ P)
    (hprecision : E + 2 + (B.rank : ℝ) * (R + 10) ≤ P)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) f g) (z : ZMod N) :
    (𝔼 s ∈ B.carrier, 𝔼 t ∈ B.carrier, (f (z + s + t) - g (z + s + t))) ≤ Real.exp (-E) := by
  sorry

end Erdos3.CyclicBohr.Set

end

end OAI
end
