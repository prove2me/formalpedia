-- Prove2me | Theorems.Thm_OAI_Erdos3_RationalFilteredNilmanifold_exists_anchored_observation_partition_s2
-- name    : OAI.Erdos3.RationalFilteredNilmanifold.exists_anchored_observation_partition_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:07:19.691658+00:00
-- url     : https://prove2.me/theorems/9a5643ce-63ec-4521-8a19-9306f4aeeac0
-- title:
--   A partition of unity on Z/NZ by positive niltests whose pieces are short, residue-pinned, and keep given nilsequence orbits close
-- statement:
--   Let $s$ and $a$ be natural numbers. Then there is a natural number $C \ge 2$ (depending only on $s$ and $a$) with the following property.
--
--   Let $\iota$ be a finite type with decidable equality. For each $i \in \iota$ let $L_i$ be a Lie algebra over $\mathbb{Q}$, with the real vector space $\mathbb{R} \otimes_{\mathbb{Q}} L_i$ given a Hausdorff topology making it a topological additive group with continuous scalar multiplication; let $d : \iota \to \mathbb{N}$, and for each $i \in \iota$ and each $b \in \{\mathrm{false}, \mathrm{true}\}$ let $E_{i,b}$ be a `RationalFilteredNilmanifold (L i) s (d i)`. This is a structure defined by OpenAI: a nilpotent Lie filtration of $L_i$ of length $s$, a $\mathbb{Q}$-basis of $L_i$ indexed by $\mathrm{Fin}(d_i)$, bases of the layers of the filtration, a subgroup (the lattice) of the associated Baker–Campbell–Hausdorff group, and a positive integer `grid` such that the lattice coordinates lie between the scaled integer grid and the grid with that denominator; its `Space` is the quotient of the real (realified) group by the image of the lattice. For each $i, b$ let $g_{i,b}$ be a polynomial orbit in the realified filtration of $E_{i,b}$ in one variable of weight $1$ (`PolynomialOrbit (fun _ : Unit => 1)`, defined by OpenAI). Let $c : \iota \to \mathbb{Z}$, let $q, N$ be positive natural numbers, and let $p, \rho$ be real numbers. Assume:
--   - $1 \le s$, $0 \le p$ and $|\iota| \le p$;
--   - for all $i, b$, `(E i b).GeometryComplexityLE p` holds (defined by OpenAI: $d_i \le p$, $\mathtt{grid} \le e^{p}$, and every Lie structure constant of the basis and every basis coordinate of every layer-basis vector is a rational of logarithmic height $\log\max(|\text{numerator}|, \text{denominator}) \le p$);
--   - $q \le e^{p}$;
--   - $0 < \rho$ and $1/\rho \le \exp((p+2)^a)$.
--
--   Then there are natural numbers $n, m > 0$ such that, writing $J = (\mathrm{Fin}\,n \times \mathbb{Z}/q\mathbb{Z}) \times \mathrm{Fin}\,m$ (so $|J| = nqm$), we have $|J| \le \exp((p+C)^C)$, and there is a family of functions $A_j : \mathbb{Z}/N\mathbb{Z} \to \mathbb{R}$, $j \in J$, such that:
--   1. for every $j$, `PositiveCyclicNiltest s N ((p + C)^C) (A j)` holds (at universe level $0$), a predicate defined by OpenAI: $A_j(x)$ is the real part of the cyclic evaluation at $x$ of a niltest that takes values in the unit interval and has complexity at most $(p+C)^C$, on some rational filtered nilmanifold whose filtration length is at most $s$;
--   2. $\sum_{j \in J} A_j(x) = 1$ for every $x \in \mathbb{Z}/N\mathbb{Z}$;
--   3. for all $j = ((k, r), l)$ and $x$: if $A_j(x) > 0$ then $x.\mathrm{val} \equiv r \pmod q$, where $x.\mathrm{val} \in \{0, \dots, N-1\}$ is the canonical representative;
--   4. for all $j, x, y$ with $A_j(x) > 0$ and $A_j(y) > 0$, the distance on the circle $\mathbb{R}/\mathbb{Z}$ between $x.\mathrm{val}/N$ and $y.\mathrm{val}/N$ is at most $\rho$;
--   5. for every $h \in \mathbb{Z}/N\mathbb{Z}$, $|\texttt{cyclicWrapExceptional}\ h\ \rho| / N \le 6\rho + 3/N$, where `cyclicWrapExceptional h ρ` (defined by OpenAI) is the set of $x \in \mathbb{Z}/N\mathbb{Z}$ with $x.\mathrm{val}$ within distance $N\rho$ of $0$, of $N$, or of $N - h.\mathrm{val}$;
--   6. using on each `(E i b).Space` the metric `(E i b).metricSpace` defined by OpenAI, and writing $\gamma_{i,b}(n)$ for `(E i b).integerOrbitPoint (g i b) n`, the image in the `Space` of the orbit $g_{i,b}$ evaluated at the integer $n$:
--      - for all $j, x, y$ with $A_j(x) > 0$, $A_j(y) > 0$, and every $i$: $\operatorname{dist}(\gamma_{i,\mathrm{false}}(x.\mathrm{val} + c_i), \gamma_{i,\mathrm{false}}(y.\mathrm{val} + c_i)) \le \rho$;
--      - for all $h \in \mathbb{Z}/N\mathbb{Z}$, $b \in \{0, 1\}$, $j, k \in J$ and $x, y \in \mathbb{Z}/N\mathbb{Z}$ with $x, y \notin \texttt{cyclicWrapExceptional}\ h\ \rho$, $A_j(x) A_k(x+h) > 0$ and $A_j(y) A_k(y+h) > 0$, and every $i$: $\operatorname{dist}(\gamma_{i,\mathrm{true}}(x.\mathrm{val} + h.\mathrm{val} - bN), \gamma_{i,\mathrm{true}}(y.\mathrm{val} + h.\mathrm{val} - bN)) \le \rho$.
--
--   Lean: `OAI.Erdos3.RationalFilteredNilmanifold.exists_anchored_observation_partition_s2`, which states OpenAI's `OAI.Erdos3.RationalFilteredNilmanifold.exists_anchored_observation_partition` (in `lean/OAI/Combinatorics/Progressions/Sampling/AnchoredObservationPartition.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B142` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/AnchoredObservationPartition.lean (declaration OAI.Erdos3.RationalFilteredNilmanifold.exists_anchored_observation_partition)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B142

section

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_anchored_observation_partition_s2 (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {d : ι → ℕ} (E : ∀ i, Bool → RationalFilteredNilmanifold (L i) s (d i))
      (g : ∀ i b, (E i b).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      (c : ι → ℤ) (q N : ℕ) [NeZero q] [NeZero N] {p ρ : ℝ},
      1 ≤ s → 0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i b, (E i b).GeometryComplexityLE p) →
      (q : ℝ) ≤ Real.exp p → 0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n m : ℕ, 0 < n ∧ 0 < m ∧
        (Fintype.card ((Fin n × ZMod q) × Fin m) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ A : ((Fin n × ZMod q) × Fin m) → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} s N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          (∀ j x, 0 < A j x → (x.val : ZMod q) = j.1.2) ∧
          (∀ j x y, 0 < A j x → 0 < A j y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) ∧
          (∀ h : ZMod N, ((cyclicWrapExceptional h ρ).card : ℝ) / N ≤ 6 * ρ + 3 / N) ∧
          (letI : ∀ i b, MetricSpace (E i b).Space := fun i b => (E i b).metricSpace
           (∀ j x y, 0 < A j x → 0 < A j y → ∀ i,
             dist ((E i false).integerOrbitPoint (g i false) ((x.val : ℤ) + c i))
               ((E i false).integerOrbitPoint (g i false) ((y.val : ℤ) + c i)) ≤ ρ) ∧
           ∀ (h : ZMod N) (b : Fin 2) j k x y,
             x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
             0 < A j x * A k (x + h) → 0 < A j y * A k (y + h) → ∀ i,
               dist ((E i true).integerOrbitPoint (g i true) ((x.val : ℤ) + h.val - (b.val : ℤ) * N))
                 ((E i true).integerOrbitPoint (g i true) ((y.val : ℤ) + h.val - (b.val : ℤ) * N)) ≤ ρ) := by
  sorry

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end
