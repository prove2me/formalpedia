-- Prove2me | Theorems.Thm_HGASUndecidable_Main_theorem_2_4
-- name    : HGASUndecidable.Main.theorem_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:15:33.80716+00:00
-- url     : https://prove2.me/theorems/bfb81c3a-19ab-4812-b33e-fbf34a9f03ec
-- title:
--   Theorem 2.4 — computable lift of degree 2k+1 on R^n to degree 3 on R^m, m = C(n+k−1, k), preserving GAS and Lyapunov stability, uniformly in (n, k)
-- statement:
--   One total computable function on input field codes works simultaneously for every n ≥ 1 and k ≥ 1. The input degree is 2k+1 and the output dimension is exactly the binomial coefficient. Theorem 2.4 (Reduction to degree three). Fix n ≥ 1 and k ≥ 1, and put m = \binom{n+k−1}{k}. There is a computable map which sends the rational coefficients of a homogeneous polynomial vector field F : R^n → R^n of degree 2k + 1 to the rational coefficients of a homogeneous polynomial vector field H : R^m → R^m of degree three such that 0 is GAS for ẋ = F(x) ⇐⇒ 0 is GAS for ẏ = H(y), (2.5) 0 is Lyapunov stable for ẋ = F(x) ⇐⇒ 0 is Lyapunov stable for ẏ = H(y). (2.6) The map can be chosen uniformly in (n, k) (Proposition 11.9).
--
--   Differences from the source:
--   - encoding: Euclidean spaces with coordinates numbered from one → State n = EuclideanSpace ℝ (Fin n), with coordinates numbered from zero; reason: the coordinate identification preserves the Euclidean norm and every instance
--   - encoding: unique maximal solutions, with existence for all forward times included in stability → HasDerivWithinAt on [0,∞), explicit forward existence, and convergence of every forward solution; reason: polynomial fields are locally Lipschitz, so uniqueness and continuation make these formulations equivalent
--   - encoding: one fixed reasonable code for rational homogeneous polynomial vector fields → Encodable encoding of (dimension, declared degree, finite coordinate/exponent-list/rational-coefficient triples), with normalized support validation; reason: all rational fields have such finite representations; duplicate monomials are combined and invalid codes are negative instances
--   - encoding: Turing-machine recursive enumerability and total computability → Mathlib REPred, ComputablePred, Computable, and ManyOneReducible using partial recursive functions; reason: these are equivalent computability notions under effective translations
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), Theorem 2.4, printed p. 5-6 (PDF 7-8)

import Definitions.Def_HGASUndecidable_Main_Codes

open Filter Topology MeasureTheory
open scoped BigOperators

namespace HGASUndecidable.Main

theorem theorem_2_4 : ∃ f : ℕ → ℕ, Computable f ∧
    ∀ (n k : ℕ), 1 ≤ n → 1 ≤ k → ∀ c : RawFieldCode,
      ValidCode c → c.1 = n → c.2.1 = 2*k+1 →
      ∃ h : RawFieldCode, decodeField (f (Encodable.encode c)) = some h ∧ ValidCode h ∧
        h.1 = Nat.choose (n+k-1) k ∧ h.2.1 = 3 ∧
        (GAS (codeField c) ↔ GAS (codeField h)) ∧
        (LyapunovStable (codeField c) ↔ LyapunovStable (codeField h)) := by sorry

end HGASUndecidable.Main
