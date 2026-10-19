-- Prove2me | Theorems.Thm_OAI_Erdos3_CellRefinement_exists_quantitative_bohr_bound_s2
-- name    : OAI.Erdos3.CellRefinement.exists_quantitative_bohr_bound_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:47:47.060492+00:00
-- url     : https://prove2.me/theorems/f82ec333-5ec2-4eca-b708-63dcbf169b84
-- title:
--   A quantitative Bohr-set cell bilinear bound for A minus (1+ε)B under a niltest upper comparison
-- statement:
--   Let $\varepsilon > 0$ be real. Then there is a real number $H \ge 0$ with the following property.
--
--   Let $N \ge 1$ be a natural number, let $B_0$ be a `CyclicBohr.Set N` (defined by OpenAI: a finite set of frequencies $r \in \mathbb{Z}/N\mathbb{Z}$ together with a radius $\rho \ge 0$; its carrier is the set of $x \in \mathbb{Z}/N\mathbb{Z}$ with $\lvert 1 - \chi_r(x)\rvert \le \rho$ for every frequency $r$, where $\chi_r$ is the additive character attached to $r$, and its rank is the number of frequencies), and let $p, R, P, W$ be real numbers. Assume:
--   - $B_0$ satisfies `IsRankRegular` (defined by OpenAI: with $d = 2\max(\operatorname{rank} B_0, 1)$, for every real $0 \le \kappa \le 1/(100d)$ the carriers of the dilates of $B_0$ by $1-\kappa$ and $1+\kappa$ have sizes at least $(1 - 100 d\kappa)\lvert B_0\rvert$ and at most $(1 + 100 d \kappa)\lvert B_0 \rvert$ respectively, where $\lvert B_0\rvert$ is the size of the carrier of $B_0$);
--   - $0 < \rho \le 2$ for the radius $\rho$ of $B_0$, and $1 \le \operatorname{rank} B_0$;
--   - $512 \le p$ and $32/(1 - c) \le p$, where $c = $ `refinementContraction ε` $= 1 - \texttt{localMomentGain}(\texttt{flatComparisonDelta}\ \varepsilon)/1081600$ (explicit real functions defined by OpenAI);
--   - $0 \le R$ and $e^{-R} \le \rho$.
--
--   Let $A, B : \mathbb{Z}/N\mathbb{Z} \to \mathbb{R}$ be functions with $0 \le A(r) \le e^{p}$ and $0 \le B(r) \le e^{p}$ for all $r$, and assume $0 \le W \le e^{p/8}$ and $\lvert A(r) - (1+\varepsilon) B(r)\rvert \le W$ for all $r$. Assume `CyclicNiltestUpperComparison 1 N P (exp (-P)) A B` holds (defined by OpenAI, at universe level $0$): for every rational filtered nilmanifold $D$ (`RationalFilteredNilmanifold L s dim`, with Lie algebra $L$ in universe $0$ and the topological-vector-space instances on $\mathbb{R} \otimes_{\mathbb{Q}} L$) of step $s \le 1$ and every one-variable niltest $T$ on $D$ (an `D.Niltest` with unit weight) that is unit-interval valued (its observable takes values in $[0,1] \subset \mathbb{C}$) and has complexity at most $P$ (`T.ComplexityLE P`), the average over $x \in \mathbb{Z}/N\mathbb{Z}$ of $(A(x) - B(x)) \cdot \operatorname{Re} T(x)$ is at most $e^{-P}$, where $T(x)$ is `T.evalCyclic N` evaluated at the constant function $x$.
--
--   Finally assume the budget condition: with $n = \lceil (p/4)/(1 - c) \rceil$ (natural-number ceiling), $d = \operatorname{rank} B_0 + n \cdot \texttt{unbalancedRankExtra}(\texttt{localMomentGain}(\texttt{flatComparisonDelta}\ \varepsilon), p, H)$ (a natural number) and $\mathrm{loss} = $ `refinementRoundLoss d p H ε`, we have `refinementComparisonBudget d p (R + n * loss) ε` $\le P$ (these are explicit functions defined by OpenAI).
--
--   Then `CellBilinearBound` holds for the carrier $C$ of $B_0$, the function $a(r) = A(r) - (1+\varepsilon)B(r)$ and the constant $2e^{-p/8}$. By OpenAI's definition this means: for every $o \in \mathbb{Z}/N\mathbb{Z}$ and all functions $f, g : \mathbb{Z}/N\mathbb{Z} \to [0,1]$ vanishing outside $C$,
--   $$\mathbb{E}_{x \in C}\,\mathbb{E}_{y \in C}\, f(x)\, g(y)\, a(o + x + y) \le 2e^{-p/8} \Bigl(\mathbb{E}_{x\in C} f(x) \cdot \mathbb{E}_{x \in C} g(x)\Bigr)^{1/4}.$$
--
--   Lean: `OAI.Erdos3.CellRefinement.exists_quantitative_bohr_bound_s2`, which states OpenAI's `OAI.Erdos3.CellRefinement.exists_quantitative_bohr_bound` (in `lean/OAI/Combinatorics/Progressions/Fourier/QuantitativeBohrBound.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B130` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Fourier/QuantitativeBohrBound.lean (declaration OAI.Erdos3.CellRefinement.exists_quantitative_bohr_bound)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B130

section

namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution

theorem exists_quantitative_bohr_bound_s2 {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (N : ℕ) [NeZero N] (B₀ : CyclicBohr.Set N) (p R P W : ℝ),
      B₀.IsRankRegular → 0 < B₀.radius → B₀.radius ≤ 2 → 1 ≤ B₀.rank →
      512 ≤ p → 32 / (1 - refinementContraction epsilon) ≤ p → 0 ≤ R →
      Real.exp (-R) ≤ B₀.radius →
      ∀ A B : ZMod N → ℝ,
      (∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p) → (∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p) →
      0 ≤ W → W ≤ Real.exp (p / 8) → (∀ r, |A r - (1 + epsilon) * B r| ≤ W) →
      CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) A B →
      (let n := ⌈(p / 4) / (1 - refinementContraction epsilon)⌉₊
       let d := B₀.rank + n * unbalancedRankExtra (localMomentGain (flatComparisonDelta epsilon)) p H
       let loss := refinementRoundLoss d p H epsilon
       refinementComparisonBudget d p (R + n * loss) epsilon ≤ P) →
      CellBilinearBound B₀.carrier (fun r => A r - (1 + epsilon) * B r)
        (2 * Real.exp (-p / 8)) := by
  sorry

end Erdos3.CellRefinement

end

end OAI
end
