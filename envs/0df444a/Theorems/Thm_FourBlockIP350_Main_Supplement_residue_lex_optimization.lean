-- Prove2me | Theorems.Thm_FourBlockIP350_Main_Supplement_residue_lex_optimization
-- name    : FourBlockIP350.Main.Supplement.residue_lex_optimization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:10:34.397093+00:00
-- url     : https://prove2.me/theorems/a2f16568-b3e5-49fe-947d-4a15e7de0f0b
-- title:
--   Lemma B.7 — Comparison-oracle optimization within a residue class
-- statement:
--   Let $I$ be a 4-block instance with $k,n\ge1$, local blocks bounded by $\bar\Delta\ge1$ and finite integral bounds with nonempty intervals; let $\Phi$ be separable convex, given by a comparison oracle whose answer to $(z,z')$ costs $(1+|I|+\operatorname{enc}(z,z'))^e$. Let $N>0$ have the uniform dilation property of Proposition 2.6 for blocks of size $2k$, let $M=kN$, and let $q\in\{0,\dots,M-1\}^k$.
--
--   There is one oracle machine $P$ such that for every exponent $e$ there are a computable $f_1$ and an exponent $d$ with the following property. On input $(I,N,q)$, within $f_1(k,\bar\Delta)(1+|I|+\operatorname{enc}(N))^d$ charged steps, $P$ either
--
--   1. reports that no global vector $x$ with $\ell^{(0)}\le x\le u^{(0)}$ is congruent to $q$ modulo $M$ (and this is true), or
--   2. outputs a pair $(x_q,y_q)$ with
--   $$x_q\equiv q\pmod M,\qquad \ell^{(0)}\le x_q\le u^{(0)},\qquad y_q\in Y,$$
--   which lexicographically minimizes
--   $$(\|b-Zx-Ey\|_1,\ \Phi(x,y))\qquad (B.6)$$
--   over all pairs $(x,y)$ with $x\equiv q\pmod M$, $\ell^{(0)}\le x\le u^{(0)}$ and $y\in Y$.
--
--   The machine accesses $\Phi$ only through the comparison oracle and never evaluates a numerical value of $\Phi$. This is the per-residue step of Theorem B.2.
--
--   Differences from the source:
--   - encoding: time f1(k, Δbar)(|I| + log N)^{O(1)} with an oracle answering in (|I| + enc(z, z'))^{O(1)} → one oracle multitape machine fixed before the oracle exponent e; for each e one machine-computable f1 and one natural exponent d; bound f1(k, Δbar)(1+|I|+|enc(N)|)^d including the charged oracle time; reason: the binary-time convention made explicit; for positive N the self-delimiting length of N is Theta(1+log N), and the residue q has length O(k(1+log(kN))), absorbed in the bound
--   - generalization: N is the positive integer provided by Proposition 2.6 for Q = [E I] → every N > 0 with UniformDilation (2*k) Δbar N, supplied as input; reason: the N of Proposition 2.6 (published uniform_idp at block size 2k) has this property, so the statement specializes to the source's
--   - encoding: Δbar is the largest absolute entry of the blocks B, D → any Δ ≥ 1 bounding those entries; reason: Δbar ≥ 1 is a standing assumption (p. 2); the statement at Δ = Δbar is the source's
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 26, Lemma B.7 (proof pp. 26–30), with (B.6)

import Mathlib
import Definitions.Def_FourBlockIP350_Main_Supplement_OracleTuring
import Definitions.Def_FourBlockIP350_Main_Supplement_SeparableIP
import Definitions.Def_FourBlockIP350_Main_Decomposition

open scoped BigOperators

namespace FourBlockIP350.Main.Supplement

open FourBlockIP350.Main

/-- Lemma B.7, p. 26: for `M = kN` and a residue `q ∈ {0, …, M−1}^k`, in time
`f₁(k, Δ̄)(|I| + log N)^{O(1)}` one either reports that no `x` with `ℓ⁽⁰⁾ ≤ x ≤ u⁽⁰⁾` is
congruent to `q` modulo `M`, or returns `(x_q, y_q)` in the residue class minimizing
`(‖b − Zx − Ey‖₁, Φ(x, y))` lexicographically over all pairs of the class, using only `O_Φ`. -/
theorem residue_lex_optimization :
    ∃ P : OracleTM, ∀ e : ℕ, ∃ f₁ : ℕ → ℕ → ℕ, ComputablePairFunction f₁ ∧
    ∃ d : ℕ, ∀ k n Δ N : ℕ, 0 < k → 0 < n → 0 < Δ → 0 < N →
      UniformDilation (2 * k) Δ N →
      ∀ I : FourBlock k n, I.localPart.Bounded Δ → GoodBox I →
      ∀ φ : BlockCol k n → ℝ → ℝ, SeparableConvex φ →
      ∀ O : List Bool → Ordering, IsPhiOracle φ O →
      ∀ q : ZVec k, IsResidue (period k N) q →
      ( (¬ ∃ x : ZVec k, GlobalBox I x ∧ CongrMod (period k N) x q) ∧
          P.ComputesWithin O (polyOracleCost (encConstraints I).length e)
            (encConstraints I ++ encNat N ++ encVector (List.finRange k) q) [false]
            (f₁ k Δ * (1 + (encConstraints I).length + (encNat N).length) ^ d) ) ∨
      ( ∃ xq : ZVec k, ∃ yq : LocalCol k n → ℤ,
          CongrMod (period k N) xq q ∧ GlobalBox I xq ∧ LocalBox I yq ∧
          (∀ x : ZVec k, ∀ y : LocalCol k n → ℤ,
            CongrMod (period k N) x q → GlobalBox I x → LocalBox I y →
            LexLE (resNorm I xq yq) (Phi φ (joinPoint xq yq))
              (resNorm I x y) (Phi φ (joinPoint x y))) ∧
          P.ComputesWithin O (polyOracleCost (encConstraints I).length e)
            (encConstraints I ++ encNat N ++ encVector (List.finRange k) q)
            ([true] ++ encVector (List.finRange k) xq ++ encVector (localOrder k n) yq)
            (f₁ k Δ * (1 + (encConstraints I).length + (encNat N).length) ^ d) ) := by sorry

end FourBlockIP350.Main.Supplement
