-- Prove2me | Theorems.Thm_FourBlockIP350_Main_Supplement_separable_convex_fpt
-- name    : FourBlockIP350.Main.Supplement.separable_convex_fpt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:11:13.133691+00:00
-- url     : https://prove2.me/theorems/33bc5280-bf36-449d-ab4e-196ffd1f40cf
-- title:
--   Theorem B.2 — Separable convex 4-block IP with a comparison oracle is FPT
-- statement:
--   Consider the separable convex 4-block integer program
--   $$\min\ \Phi(x,y)=\Phi^{(0)}(x)+\sum_{i=1}^n\Phi^{(i)}(y^{(i)})\quad\text{s.t.}\quad Zx+Ey=b,\ \ \ell\le(x,y)\le u,\ \ (x,y)\ \text{integral},$$
--   with block dimension $k\ge1$, $n\ge1$ nonuniform bricks, local blocks $B^{(i)},D^{(i)}$ with entries bounded by $\bar\Delta\ge1$, arbitrary integral global-column blocks, right-hand side and **finite integral bounds** (intervals may be empty). Every component $\phi_j^{(i)}:\mathbb R\to\mathbb R$ of $\Phi$ is convex and finite-valued, and $\Phi$ is accessible only through a comparison oracle $O_\Phi$ which, for any integer points $z,z'\in\mathbb Z^{(n+1)k}$ (also outside the bounds), reports which of $\Phi(z)<\Phi(z')$, $=$, $>$ holds, in time $(1+|I|+\operatorname{enc}(z,z'))^e$.
--
--   There is one oracle machine $P$ such that for every exponent $e$ there are a computable function $f$ and an exponent $d$ such that, for every such instance $I$, every such objective and every oracle consistent with it, $P$ on input $I$ halts within
--   $$f(k,\bar\Delta)\cdot(1+|I|)^d$$
--   charged steps and outputs either an integral $(x^\star,y^\star)$ satisfying all equations and bounds with $\Phi(x^\star,y^\star)\le\Phi(\bar x,\bar y)$ for every feasible $(\bar x,\bar y)$, or a correct report that the instance is infeasible. Here $|I|$ is the binary length of the constraint data and bounds; the objective is not input.
--
--   The algorithm uses only comparisons of objective values: it needs neither numerical objective evaluations nor bounds on the magnitudes or differences of objective values. It extends the mission's main theorem from linear costs to separable convex costs, for finite bounds.
--
--   Differences from the source:
--   - encoding: time f(k, Δbar)|I|^{O(1)} with an oracle answering in (|I| + enc(z, z'))^{O(1)} → one oracle multitape machine fixed before the oracle exponent e; for each e one machine-computable f and one natural exponent d; bound f(k, Δbar)(1+|I|)^d including the charged oracle time; reason: makes the source's binary-time convention with polynomial-time oracle explicit; the algorithm does not know e
--   - encoding: Δbar is the largest absolute entry of the blocks B, D → any Δ ≥ 1 bounding those entries; reason: Δbar ≥ 1 is a standing assumption (p. 2); the statement at Δ = Δbar is the source's
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 21, Theorem B.2 (proof pp. 30–31), with (4-Block IP) and the comparison oracle of §B.1

import Mathlib
import Definitions.Def_FourBlockIP350_Main_Supplement_OracleTuring
import Definitions.Def_FourBlockIP350_Main_Supplement_SeparableIP

open scoped BigOperators

namespace FourBlockIP350.Main.Supplement

open FourBlockIP350.Main

/-- Theorem B.2, p. 21: a separable convex 4-block integer program with finite integral bounds,
whose objective is accessible only through a comparison oracle, is solved (an optimal solution,
or infeasibility) in time `f(k, Δ̄)|I|^{O(1)}` by one oracle machine. -/
theorem separable_convex_fpt :
    ∃ P : OracleTM, ∀ e : ℕ, ∃ f : ℕ → ℕ → ℕ, ComputablePairFunction f ∧
    ∃ d : ℕ, ∀ k n Δ : ℕ, 0 < k → 0 < n → 0 < Δ →
      ∀ I : FourBlock k n, I.localPart.Bounded Δ → FiniteBounds I →
      ∀ φ : BlockCol k n → ℝ → ℝ, SeparableConvex φ →
      ∀ O : List Bool → Ordering, IsPhiOracle φ O →
      ∃ a : SepAnswer (BlockCol k n), SepCorrect I φ a ∧
        P.ComputesWithin O (polyOracleCost (encConstraints I).length e)
          (encConstraints I) (encSepAnswer (blockOrder k n) a)
          (f k Δ * (1 + (encConstraints I).length) ^ d) := by sorry

end FourBlockIP350.Main.Supplement
