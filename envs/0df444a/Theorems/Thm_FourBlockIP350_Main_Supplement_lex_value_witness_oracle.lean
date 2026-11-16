-- Prove2me | Theorems.Thm_FourBlockIP350_Main_Supplement_lex_value_witness_oracle
-- name    : FourBlockIP350.Main.Supplement.lex_value_witness_oracle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:07:41.50198+00:00
-- url     : https://prove2.me/theorems/d353faec-1fdc-4ab7-9010-6f92894b102b
-- title:
--   Lemma B.3 — Lexicographic value-and-witness oracle
-- statement:
--   Let $I$ be a 4-block instance with block dimension $k\ge1$, $n\ge1$ bricks, local blocks $B^{(i)},D^{(i)}$ with entries bounded by $\bar\Delta\ge1$ in absolute value, and finite integral bounds with nonempty intervals, so that $Y=\{y\in\mathbb Z^{nk}:\ell^{(1:n)}\le y\le u^{(1:n)}\}$ is finite and nonempty. Let $\Phi$ be a separable convex objective accessible through a comparison oracle $O_\Phi$ whose answer to a query $(z,z')$ costs $(1+|I|+\operatorname{enc}(z,z'))^e$. For $x\in\mathbb Z^k$ let
--   $$r(x)=\min_{y\in Y}\|b-Zx-Ey\|_1,\qquad y_x\in\operatorname{argmin}\{\Phi(x,y):y\in Y,\ \|b-Zx-Ey\|_1=r(x)\}.$$
--   There are two oracle machines $P_1,P_2$ such that for every exponent $e$ there are a computable $g$ and an exponent $d$ with:
--
--   1. for every $x\in\mathbb Z^k$, $P_1$ on input $(I,x)$ outputs $r(x)$ and a vector $y_x$ as above within $g(k,\bar\Delta)(1+|I|+\operatorname{enc}(x))^d$ charged steps;
--   2. for all $x,x'\in\mathbb Z^k$, $P_2$ on input $(I,x,x')$ outputs the lexicographic comparison of $(r(x),\Phi(x,y_x))$ and $(r(x'),\Phi(x',y_{x'}))$ within $g(k,\bar\Delta)(1+|I|+\operatorname{enc}(x)+\operatorname{enc}(x'))^d$ charged steps.
--
--   Both hold for every instance, every separable convex $\Phi$ and every oracle consistent with $\Phi$. The machines access $\Phi$ only through the oracle, so no objective value is ever evaluated.
--
--   This is the step that replaces the numerical exact penalty of the linear case by a lexicographic objective.
--
--   **Formalization Note** Time is counted on the base multitape model extended by a query tape; every query is charged its oracle answer time. The compared value $\Phi(x,y_x)$ does not depend on the choice of $y_x$, and the statement requires the answer to agree for every choice.
--
--   Differences from the source:
--   - encoding: time g(k, Δbar)(|I| + enc(x))^{O(1)} with an oracle answering in (|I| + enc(z, z'))^{O(1)} → one oracle multitape machine per conclusion, fixed before the oracle exponent e; for each e one machine-computable g and one natural exponent d; bound g(k, Δbar)(1+|I|+|enc(x)|)^d including the charged oracle time; reason: makes the source's binary-time convention with polynomial-time oracle explicit; the machines are uniform in e as the source's algorithm is
--   - encoding: Δbar is the largest absolute entry of the blocks B, D → any Δ ≥ 1 bounding those entries; reason: Δbar ≥ 1 is a standing assumption (p. 2) and the source's bound is attained at Δ = Δbar
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 22, Lemma B.3, with (B.1), (B.2) and the standing assumptions of §B.1, p. 21

import Mathlib
import Definitions.Def_FourBlockIP350_Main_Supplement_OracleTuring
import Definitions.Def_FourBlockIP350_Main_Supplement_SeparableIP

open scoped BigOperators

namespace FourBlockIP350.Main.Supplement

open FourBlockIP350.Main

/-- Lemma B.3, p. 22: `r(x)` and a witness `y_x` of (B.2) are computed, and the pairs
`(r(x), Φ(x, y_x))`, `(r(x'), Φ(x', y_x'))` are compared, in time
`g(k, Δ̄)(|I| + enc(·))^{O(1)}`, by oracle machines whose only access to `Φ` is `O_Φ`. -/
theorem lex_value_witness_oracle :
    ∃ P₁ P₂ : OracleTM, ∀ e : ℕ, ∃ g : ℕ → ℕ → ℕ, ComputablePairFunction g ∧
    ∃ d : ℕ, ∀ k n Δ : ℕ, 0 < k → 0 < n → 0 < Δ →
      ∀ I : FourBlock k n, I.localPart.Bounded Δ → GoodBox I →
      ∀ φ : BlockCol k n → ℝ → ℝ, SeparableConvex φ →
      ∀ O : List Bool → Ordering, IsPhiOracle φ O →
      (∀ x : ZVec k, ∃ y : LocalCol k n → ℤ, IsLexWitness I φ x y ∧
        P₁.ComputesWithin O (polyOracleCost (encConstraints I).length e)
          (encConstraints I ++ encVector (List.finRange k) x)
          (encInt (resNorm I x y) ++ encVector (localOrder k n) y)
          (g k Δ * (1 + (encConstraints I).length +
            (encVector (List.finRange k) x).length) ^ d)) ∧
      (∀ x x' : ZVec k, ∃ o : Ordering,
        (∀ y y' : LocalCol k n → ℤ, IsLexWitness I φ x y → IsLexWitness I φ x' y' →
          o = lexCompare (resNorm I x y) (Phi φ (joinPoint x y))
                (resNorm I x' y') (Phi φ (joinPoint x' y'))) ∧
        P₂.ComputesWithin O (polyOracleCost (encConstraints I).length e)
          (encConstraints I ++ encVector (List.finRange k) x ++ encVector (List.finRange k) x')
          (encOrdering o)
          (g k Δ * (1 + (encConstraints I).length + (encVector (List.finRange k) x).length +
            (encVector (List.finRange k) x').length) ^ d)) := by sorry

end FourBlockIP350.Main.Supplement
