-- Prove2me | Theorems.Thm_OAI_Erdos3_polynomial_affine_weightedCubeBlock_major_arc_s2
-- name    : OAI.Erdos3.polynomial_affine_weightedCubeBlock_major_arc_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:16:47.177702+00:00
-- url     : https://prove2.me/theorems/6b457b37-adfa-4e4f-8b20-0b97f717d681
-- title:
--   A large exponential bias over a product of weighted scalar cube sources puts the Boolean block coefficients on a common major arc
-- statement:
--   Let $n$ be a natural number and $I$ a finite type with decidable equality. For each $j \in \{0, \dots, n\}$ let $s_j$ be a `NormalizedScalarCubeSource I` (a structure defined by OpenAI: a length $\ell_j = $ `(s j).length` $> 0$, a modulus bound, moduli $m_{j,i} = $ `(s j).modulus i` $> 0$ and residues indexed by $i \in \mathrm{Option}\,I$, and a bounded Lipschitz weight, normalized so that a reweighted residue law `(s j).source` is a probability distribution on the integer cube $\mathrm{Option}\,I \to [-\ell_j, \ell_j) \cap \mathbb{Z}$). Let $A \ge 0$ be a real number such that `Real.smoothTransition` (Mathlib's smooth transition function from $0$ to $1$) is $A$-Lipschitz, and let $U, \zeta$ be real numbers. Assume:
--   - `ScalarCubePrimitiveBudget (s j) A U` for every $j$ (a structure of OpenAI collecting the bounds $1 \le U$, $|I| + 1 \le U$, and that the modulus bound, weight bound and weight Lipschitz constant of $s_j$ and several explicit constants depending on $I$, $A$ and the modulus bound are all at most $U$);
--   - $0 < \zeta \le 1$;
--   - `localizedMajorArcLengthBudget n U ζ` $\le \ell_j$ for every $j$ (an explicit real quantity of OpenAI).
--
--   Let $u : \{0,\dots,n\} \to (\mathrm{Option}\,I \to \mathbb{R})$ and $v : \{0,\dots,n\} \to (\mathrm{Option}\,I \to \mathbb{N})$ with $v_{j,i} > 0$ and $v_{j,i}\, m_{j,i} \le U$ for all $j, i$. Let $\xi : \mathrm{Finset}\,I \to \mathbb{R}$, and let $\mathcal{J}$ be a finite set of finite subsets of $I$ with $|S| \le n+1$ for every $S \in \mathcal{J}$. For a point $z = (z_j)_j$ of the product of the cubes, set $a_j(z) = $ `affineCubeCoordinates (u j) (v j) z_j`, the function $i \mapsto u_{j,i} + v_{j,i} z_{j,i}$ on $\mathrm{Option}\,I$, and let $\Phi(z) = $ `booleanBlockPhase ξ a(z)`, which by OpenAI's definition is
--   $$\Phi(z) = \sum_{S \subseteq I} \xi(S) \sum_{T \subseteq S} (-1)^{|S \setminus T|} \prod_{j=0}^{n} \Bigl(a_j(z)(\mathrm{none}) + \sum_{i \in T} a_j(z)(i)\Bigr).$$
--   Assume the bias bound
--   $$\zeta \le \Bigl|\, \mathbb{E}_{z}\, e^{2\pi i \Phi(z)} \Bigr|,$$
--   where $z$ is distributed according to the product of the probability distributions `(s j).source`, $j = 0, \dots, n$.
--
--   Then there exist a natural number $D > 0$ with
--   $$D \le \bigl(\texttt{localizedMajorArcBudget}\ n\ U\ \zeta \cdot U^{n+1}\bigr)^{|\mathcal{J}|}$$
--   and integers $a_S$ ($S \in \mathcal{J}$) such that for every $S \in \mathcal{J}$,
--   $$\Bigl|\xi(S) - \frac{a_S}{D}\Bigr| \le \frac{\texttt{localizedMajorArcErrorBudget}\ n\ U\ \zeta}{\prod_{j=0}^{n} \ell_j}.$$
--   Here `localizedMajorArcBudget n U ζ` and `localizedMajorArcErrorBudget n U ζ` are explicit real quantities defined by OpenAI.
--
--   Lean: `OAI.Erdos3.polynomial_affine_weightedCubeBlock_major_arc_s2`, which states OpenAI's `OAI.Erdos3.polynomial_affine_weightedCubeBlock_major_arc` (in `lean/OAI/Combinatorics/Progressions/Fourier/PolynomialWeightedCubeMajorArc.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B085`, `OAIE3v2B136` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Fourier/PolynomialWeightedCubeMajorArc.lean (declaration OAI.Erdos3.polynomial_affine_weightedCubeBlock_major_arc)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B085
import Definitions.Def_OAIE3v2B136

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal
open CircleFourier

theorem polynomial_affine_weightedCubeBlock_major_arc_s2 {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U ζ : ℝ}
    (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hlen : ∀ j, localizedMajorArcLengthBudget n U ζ ≤ (s j).length)
    (u : Fin (n + 1) → Option I → ℝ) (v : Fin (n + 1) → Option I → ℕ)
    (hv : ∀ j i, 0 < v j i) (hstride : ∀ j i, ((v j i * (s j).modulus i : ℕ) : ℝ) ≤ U)
    (ξ : Finset I → ℝ) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hbias : ζ ≤ ‖(FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
      (fun z => character ((booleanBlockPhase ξ
        (fun j => affineCubeCoordinates (u j) (v j) (fun i => (z j i : ℝ))) : ℝ) : CircleFourier.Circle))‖) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ (localizedMajorArcBudget n U ζ * U ^ (n + 1)) ^ J.card ∧
      ∃ a : J → ℤ, ∀ S : J, |ξ S - (a S : ℝ) / D| ≤
        localizedMajorArcErrorBudget n U ζ / ∏ j, ((s j).length : ℝ) := by
  sorry

end Erdos3

end

end OAI
end
