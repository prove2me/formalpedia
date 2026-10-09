-- Prove2me | Theorems.Thm_OAI_Erdos3_RationalFilteredNilmanifold_exists_scored_native_chart
-- name    : OAI.Erdos3.RationalFilteredNilmanifold.exists_scored_native_chart
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-09T00:39:15.135084+00:00
-- url     : https://prove2.me/theorems/5c41c78b-18f9-40de-85aa-3feeecb85831
-- title:
--   A scored niltest can be localized to a single chart with polynomially controlled data
-- statement:
--   For every natural number $s$ there is a natural number $C \ge 2$ with the following property. Let $\sigma$, $X$, $L$ be types with $X$ finite and $L$ a Lie algebra over $\mathbb{Q}$, let $d \in \mathbb{N}$, and give $\mathbb{R} \otimes_{\mathbb{Q}} L$ a Hausdorff topology making it a topological additive group with continuous real scalar multiplication. Let $D$ be a `RationalFilteredNilmanifold L s d` (OpenAI's structure bundling a nilpotent filtration of $L$ of length $s$, a $\mathbb{Q}$-basis of $L$ indexed by $\mathrm{Fin}\ d$, bases of the layers, a lattice subgroup and a grid), let $w : \sigma \to \mathbb{N}$, and let $T$ be a `D.Niltest w` (OpenAI's structure bundling a polynomial orbit with weights $w$ in the realified group and a bounded Lipschitz observable $D.\mathrm{Space} \to \mathbb{C}$, with $T.\mathrm{eval}(x) \in \mathbb{C}$ for $x \in \mathbb{Z}^\sigma$ the observable at the image of the orbit point). Let $a : X \to \mathbb{R}$, $u : X \to \mathbb{Z}^\sigma$ and $p \in \mathbb{R}$, and assume $0 \le p$, `T.ComplexityLE p` (OpenAI's complexity bound: the geometry of $D$ has complexity at most $p$ and $\log(2 + \text{norm bound} + \text{Lipschitz bound}) \le p$), `T.UnitIntervalValued` (the observable takes values in $[0,1] \subseteq \mathbb{R}$), and $e^{-p} \le \mathbb{E}_{x \in X}\, a(x)\,\mathrm{Re}\,T.\mathrm{eval}(u(x))$. Then, with $D.\mathrm{Space}$ carrying OpenAI's metric `D.metricSpace`, there exist $r \in \mathbb{R}_{\ge 0}$, an element $z$ of the real group `D.RealGroup`, and an open partial homeomorphism $\varphi$ from $\mathbb{R}^{d}$ (sup metric) to $D.\mathrm{Space}$ such that: $0 < r \le 1$ and $1/r \le \exp((p+2)^C)$; every coordinate of $z$ in the real base change of $D$'s basis has absolute value at most $\exp((p+2)^C)$; $\varphi(v)$ is the image in the quotient of $z \cdot \Psi^{-1}(v)$ for every $v$, where $\Psi$ is `NilpotentLieBCHGroup.basisHomeomorph` of the real base change of $D$'s basis; the source of $\varphi$ is the open cube $\{v : |v_i| < r \text{ for all } i\}$; and there is a `D.Niltest w` $U$ with the same orbit as $T$ that is unit-interval-valued, satisfies `U.ComplexityLE ((p+2)^C)`, has compactly supported observable whose topological support lies in the target of $\varphi$ and in $\varphi$ of the closed ball of radius $3r/4$ about $0$, satisfies $\exp(-(p+2)^C) \le \mathbb{E}_{x}\, a(x)\,\mathrm{Re}\,U.\mathrm{eval}(u(x))$, and for which some $K \in \mathbb{R}_{\ge 0}$ with $K \le \exp((p+2)^C)$ makes $\varphi$ $K$-Lipschitz on its source.
--
--   Lean: `OAI.Erdos3.RationalFilteredNilmanifold.exists_scored_native_chart` in `lean/OAI/Combinatorics/Progressions/Sampling/IntegralScoredKernel.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B034` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/IntegralScoredKernel.lean#L12

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B034

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal BigOperators

theorem exists_scored_native_chart (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ X L : Type*} [Fintype X]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ} (T : D.Niltest w)
      (a : X → ℝ) (u : X → σ → ℤ) {p : ℝ},
      0 ≤ p → T.ComplexityLE p → T.UnitIntervalValued →
      Real.exp (-p) ≤ (𝔼 x, a x * (T.eval (u x)).re) →
      letI := D.metricSpace
      ∃ (r : ℝ≥0) (z : D.RealGroup) (phi : OpenPartialHomeomorph (Fin d → ℝ) D.Space),
        0 < r ∧ r ≤ 1 ∧ 1 / (r : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        (∀ i, |(D.basis.baseChange ℝ).repr z.coord i| ≤ Real.exp ((p + 2) ^ C)) ∧
        (∀ v, phi v = QuotientGroup.mk
          (z * (NilpotentLieBCHGroup.basisHomeomorph (D.basis.baseChange ℝ)).symm v)) ∧
        phi.source = {v | ∀ i, |v i| < (r : ℝ)} ∧
        ∃ U : D.Niltest w, U.orbit = T.orbit ∧ U.UnitIntervalValued ∧
          U.ComplexityLE ((p + 2) ^ C) ∧ HasCompactSupport U.observable ∧
          tsupport U.observable ⊆ phi.target ∧
          (Real.exp (-((p + 2) ^ C)) ≤ 𝔼 x, a x * (U.eval (u x)).re) ∧
          tsupport U.observable ⊆ phi '' Metric.closedBall 0 (3 * (r : ℝ) / 4) ∧
          ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
            LipschitzOnWith K phi phi.source := by
  sorry

end Erdos3.RationalFilteredNilmanifold
end
end OAI
