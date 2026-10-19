-- Prove2me | Theorems.Thm_OAI_Erdos3_PositiveShiftBasis_exists_prescribed_lower_inputs_s2
-- name    : OAI.Erdos3.PositiveShiftBasis.exists_prescribed_lower_inputs_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:44:15.390156+00:00
-- url     : https://prove2.me/theorems/d2a092e8-ccaf-40ae-9cf0-41b7f1e0bbc3
-- title:
--   Square-model factorization with large interval correlations for a positive shift basis
-- statement:
--   For every natural number $s$ there is a natural number $C \ge 2$ with the following property. Let $N \neq 0$ be a natural number, $q$ a real, $a, J : \mathbb Z/N \to \mathbb R$, and `B : PositiveShiftBasis s N q a J` (OpenAI's structure bundling a rational filtered nilmanifold of degree $s$ and complexity at most $q$, a natural number `B.count`, a nonempty set `B.shifts` $\subseteq \mathbb Z/N$, and for each shift $h$ and $j < \texttt{B.count}$ a niltest mode `B.mode h j` on that nilmanifold, with independent vertical frequencies and correlation bias). Let $L_i$ ($i \in \mathrm{Fin}\,\texttt{B.count} \times \mathrm{Bool}$) be Lie algebras over $\mathbb Q$ and $d_i$ natural numbers, with Hausdorff topological-vector-space structures on $\mathbb R \otimes_{\mathbb Q} L_i$; let $D_i$ be `RationalFilteredNilmanifold (L i) (s+1) (d i)`, with the same kind of topological structures on $\mathbb R \otimes_{\mathbb Q}$ of the square Lie subalgebra of the filtration of $D_i$ and of its quotient by the $(s+1)$-st layer ideal of the square filtration; let $T_i$ be niltests on $D_i$ (one variable, weight $1$); and let $H$ be a finite subset of `B.shifts`. Then for every real $p$ with $2 \le p$, $q \le p$ and $e^{-p} N \le |H|$, if every $T_i$ has complexity at most $p$ (`ComplexityLE p`) and norm bound at most $1$, and for some family $\chi_i : $ `(D i).RealGroup` $\to$ `Circle` each observable satisfies $T_i(z \cdot x) = \texttt{character}(\chi_i(z))\, T_i(x)$ for all $z$ in the realified $(s+1)$-st subgroup and all $x$, and if for every $h \in H$ and every $j$
--   $$e^{-p} \le \Bigl\| \mathbb E_{n \in \mathbb Z/N}\, \texttt{B.mode}_{h,j}(n)\; T_{(j,\mathrm{true})}(n)\; T_{(j,\mathrm{false})}(n+h) \Bigr\|$$
--   (cyclic evaluations `evalCyclic N`), then there exist `SquareModelData` $F_i$ for every $D_i$ (OpenAI's structure bundling an adapted basis, weights and grid for the square construction) such that, with $Q = (p+C)^C$:
--
--   - the full and quotient models of every $F_i$ satisfy `GeometryComplexityLE Q`, and all rational log-heights of the coordinates of the basis of $F_i$ in the basis of $D_i$ are at most $Q$;
--   - there exist $h_0 \in H$, branch choices $\mathrm{branches} : \mathrm{Fin}\,\texttt{B.count} \to \mathrm{Bool} \times \mathrm{Bool}$ and a finite set $S \subseteq H$, nonempty, with $e^{-Q} N \le |S|$, and there exist niltests $A_j$ on the quotient model of $F_{(j,\mathrm{true})}$ and $R_{h,j}$ on the quotient model of $F_{(j,\mathrm{false})}$, elements $\eta_{h,j}, \gamma_{h,j}$ of `(D (j,false)).RealGroup` and polynomial orbits $r_{h,j}$ in the realified square filtration of $D_{(j,\mathrm{false})}$, such that:
--     - each $A_j$ has norm bound $\le 1$, complexity $\le Q$, and $A_j(x) = T_{(j,\mathrm{true})}(x)\,\overline{T_{(j,\mathrm{true})}(x)}$ for all $x$;
--     - for all $h, j$: $\gamma_{h,j}$ lies in the real lattice of $D_{(j,\mathrm{false})}$; every coordinate of $\eta_{h,j}$ in the real base change of the basis of $D_{(j,\mathrm{false})}$ has absolute value $\le e^{Q}$; for every $x \in \mathbb Z$, the first projection `realSquareFstHom` of the evaluation of $r_{h,j}$ at $x$ equals $\eta_{h,j}^{-1}\, g(x + o(h, \mathrm{branches}_j.1))\, \gamma_{h,j}^{-1}$ and the second projection `realSquareSndHom` equals $g(x + o(h_0, \mathrm{branches}_j.2))$, where $g$ is the polynomial orbit of $T_{(j,\mathrm{false})}$ evaluated by `polynomialOrbitEval` and $o(h, \beta) = $ `cyclicBranchOffset h β` $= h.\mathrm{val} - (N \text{ if } \beta \text{ else } 0)$; the orbit of $R_{h,j}$ is the image of $r_{h,j}$ in the quotient by the $(s+1)$-st layer ideal (`realQuotientPolynomialOrbit`); $R_{h,j}$ has norm bound $\le 1$ and complexity $\le Q$; and $R_{h,j}(x) = T_{(j,\mathrm{false})}(x + o(h, \mathrm{branches}_j.1))\,\overline{T_{(j,\mathrm{false})}(x + o(h_0, \mathrm{branches}_j.2))}$ for all $x$;
--     - for every $h \in S$ and every $j$ there are natural numbers $\mathrm{start}, \mathrm{len}$ with $0 < \mathrm{len}$, $\mathrm{start} + \mathrm{len} \le N$, $2(\mathrm{len} - 1) < N$, $e^{-Q} N \le \mathrm{len}$, and
--   $$e^{-Q} \le \Bigl\| \mathbb E_{x \in [\mathrm{start}, \mathrm{start}+\mathrm{len})}\, \texttt{B.mode}_{h,j}(x)\, \overline{\texttt{B.mode}_{h_0,j}(x)}\, A_j(x)\, R_{h,j}(x) \Bigr\|,$$
--     the average being over the integer interval `translatedIntegerBox start len` (one variable) and the niltests evaluated by `eval`.
--
--   Lean: `OAI.Erdos3.PositiveShiftBasis.exists_prescribed_lower_inputs_s2`, which states OpenAI's `OAI.Erdos3.PositiveShiftBasis.exists_prescribed_lower_inputs` (in `lean/OAI/Combinatorics/Progressions/Estimates/NativeDetectorContradictionSpec.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B210` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/NativeDetectorContradictionSpec.lean (declaration OAI.Erdos3.PositiveShiftBasis.exists_prescribed_lower_inputs)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B210

section

namespace OAI

section

namespace Erdos3.PositiveShiftBasis

open Module NilpotentLieFiltration CircleFourier
open scoped TensorProduct BigOperators NNReal

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

theorem exists_prescribed_lower_inputs_s2 (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
      (B : PositiveShiftBasis s N q a J) {L : (Fin B.count × Bool) → Type*}
      [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : (Fin B.count × Bool) → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i))
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, T2Space (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      (T : ∀ i, (D i).Niltest (fun _ : Unit => 1))
      (H : Finset (ZMod N)), H ⊆ B.shifts →
      ∀ {p : ℝ}, 2 ≤ p → q ≤ p → Real.exp (-p) * N ≤ (H.card : ℝ) →
      (∀ i, (T i).ComplexityLE p) → (∀ i, (T i).normBound ≤ 1) →
      ∀ χ : ∀ i, (D i).RealGroup → CircleFourier.Circle,
      (∀ i z, z ∈ (D i).filtration.realification.subgroup (s + 1) → ∀ x,
        (T i).observable (z • x) = character (χ i z) * (T i).observable x) →
      (∀ h ∈ H, ∀ j, Real.exp (-p) ≤ ‖𝔼 n,
        (B.mode h j).evalCyclic N (fun _ => n) * (T (j, true)).evalCyclic N (fun _ => n) *
          (T (j, false)).evalCyclic N (fun _ => n + h)‖) →
      ∃ F : ∀ i, (D i).SquareModelData,
        (∀ i, (F i).fullModel.GeometryComplexityLE ((p + C) ^ C)) ∧
        (∀ i, (F i).quotientModel.GeometryComplexityLE ((p + C) ^ C)) ∧
        (∀ i j k, rationalLogHeight ((D i).basis.repr ((F i).basis j) k) ≤ (p + C) ^ C) ∧
        ∃ h₀ ∈ H, ∃ (branches : Fin B.count → Bool × Bool) (S : Finset (ZMod N)),
          S ⊆ H ∧ S.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (S.card : ℝ) ∧
          ∃ (A : ∀ j, (F (j, true)).quotientModel.Niltest (fun _ : Unit => 1))
            (R : ZMod N → ∀ j, (F (j, false)).quotientModel.Niltest (fun _ : Unit => 1))
            (η γ : ZMod N → ∀ j, (D (j, false)).RealGroup)
            (rSq : ZMod N → ∀ j,
              (D (j, false)).filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1)),
            (∀ j, (A j).normBound ≤ 1 ∧ (A j).ComplexityLE ((p + C) ^ C) ∧
              ∀ x, (A j).eval x = (T (j, true)).eval x * star ((T (j, true)).eval x)) ∧
            (∀ h j, γ h j ∈ (D (j, false)).realLattice ∧
              (∀ i, |((D (j, false)).basis.baseChange ℝ).repr (η h j).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
              (∀ x : Unit → ℤ,
                (D (j, false)).filtration.realSquareFstHom
                  ((D (j, false)).filtration.squareFiltration.realification.polynomialOrbitEval
                    (fun _ => 1) x (rSq h j)) =
                    (η h j)⁻¹ * (D (j, false)).filtration.realification.polynomialOrbitEval (fun _ => 1)
                      (x + fun _ => cyclicBranchOffset h (branches j).1) (T (j, false)).orbit * (γ h j)⁻¹ ∧
                (D (j, false)).filtration.realSquareSndHom
                  ((D (j, false)).filtration.squareFiltration.realification.polynomialOrbitEval
                    (fun _ => 1) x (rSq h j)) =
                    (D (j, false)).filtration.realification.polynomialOrbitEval (fun _ => 1)
                      (x + fun _ => cyclicBranchOffset h₀ (branches j).2) (T (j, false)).orbit) ∧
              (R h j).orbit = (D (j, false)).filtration.squareFiltration.realQuotientPolynomialOrbit
                ((D (j, false)).filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl (rSq h j) ∧
              (R h j).normBound ≤ 1 ∧ (R h j).ComplexityLE ((p + C) ^ C) ∧
              ∀ x, (R h j).eval x =
                (T (j, false)).eval (x + fun _ => cyclicBranchOffset h (branches j).1) *
                  star ((T (j, false)).eval (x + fun _ => cyclicBranchOffset h₀ (branches j).2))) ∧
            ∀ h ∈ S, ∀ j, ∃ start len : ℕ, 0 < len ∧ start + len ≤ N ∧
              2 * ((len : ℤ) - 1) < N ∧ Real.exp (-((p + C) ^ C)) * N ≤ (len : ℝ) ∧
              Real.exp (-((p + C) ^ C)) ≤
                ‖𝔼 x ∈ translatedIntegerBox (fun _ : Unit => (start : ℤ)) (fun _ => len),
                  (B.mode h j).eval x * star ((B.mode h₀ j).eval x) * (A j).eval x * (R h j).eval x‖ := by
  sorry

end Erdos3.PositiveShiftBasis

end

end OAI
end
