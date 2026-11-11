-- Prove2me | Theorems.Thm_IntegerRootsFN_Main_proposition_3_4
-- name    : IntegerRootsFN.Main.proposition_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:53:53.295619+00:00
-- url     : https://prove2.me/theorems/d3a7e02b-8bc9-48fa-87e7-9ebc653accdc
-- title:
--   Proposition 3.4 — rational approximations with total size and time
-- statement:
--   Let $g\in\mathbb Z[x]$ have exact degree $d\ge1$ and coefficient magnitudes less than $2^b$, for any $b\ge1$. A single uniform deterministic machine computes $d$ represented Gaussian rational numbers $\beta_i$ in time $\widetilde O(d(b+d))$, with total represented size $\widetilde O(d(b+d))$, such that
--
--   $$\forall\alpha\text{ a root of }g,\quad\exists i:\ |\alpha-\beta_i|<\tfrac18,\qquad
--   \sum_{i=1}^d\log_2\max(1,|\beta_i|)\le b+\tfrac12\log_2(d+1)+2.$$
--
--   The logs hidden in time and size involve only $d,b$, with positive constant and fixed exponents chosen before all inputs. There is no restriction $d\le b$. The finite intermediate outputs also certify the source's shift, actual coefficient reversal, relative error at its prescribed $P$, a common dyadic denominator with $B=O(P)$, nonzero $w_i$, and exact $\beta_i=q+1/w_i$. All records are charged in the same run. The final rational denominators are positive and their mathematical sizes sum the two numerator and denominator lengths.
--
--   This gives actual finite computation and aggregate output size, in addition to the analytic coverage and logarithmic-size conclusions; Pan's runtime stays a supporting proof obligation.
--
--   Differences from the source:
--   - encoding: integers n,b≥1 and coefficients given in binary → positive natural parameters, dense signed fixed-width coefficients, finite signed binary outputs; reason: this represents every source input; signs, delimiters, input reads and output writes count as machine steps
--   - encoding: uniform soft-O bit-operation bounds → one finite deterministic multitape machine and positive global C with fixed natural exponents k,l before all varying inputs, bounded by CF(1+log₂(n+1))^k(1+log₂(b+1))^l; reason: shifted logarithms cover the small inputs without changing the allowed polynomial or logarithmic scope; finite initially blank work tapes prohibit advice or assigned costs
--   - encoding: intermediate arithmetic in the specified construction on pp.8–10 → the finite dyadic circle samples, selected Gaussian integer and, for approximation, common-dyadic factors are also emitted; reason: these are computed intermediate records of the source procedure; emitting them charges their representation and pins the construction rather than assuming a successful approximation
-- source:
--   Yansong Feng, Itamar Nir, STOC 2027 submission #1353 (October 2026), p. 9, Proposition 3.4, construction and precision pp.9–10

import Mathlib
import Definitions.Def_IntegerRootsFN_Main_Binary
import Definitions.Def_IntegerRootsFN_Main_ApproximationConstruction

set_option autoImplicit false

namespace IntegerRootsFN.Main

theorem proposition_3_4 :
    ∃ M : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧ ∃ k l : ℕ,
    ∀ (d b : ℕ) (g : Polynomial ℤ), Valid g d b →
    ∃ (samples : Fin (d + 1) → ApproxGKR.GaussDyadic) (q : ℤ × ℤ)
      (B : ℕ) (ws : Fin d → ℤ × ℤ) (β : Fin d → GaussianRational),
      ApproximationTrace g d b samples q B ws β ∧
      (B : ℝ) ≤ C * approximationPrecision d b ∧
      CoversRoots (complexify g) (fun i => (β i).value) ∧
      logRootSize (fun i => (β i).value) ≤ rootSizeBound d b ∧
      (∑ i, ((β i).bitSize : ℝ)) ≤ softBound C k l d b ((d : ℝ) * (b + (d : ℝ))) ∧
      Runs M (polynomialWord g d b) (approximationOutputWord samples q B ws β)
        (softBound C k l d b ((d : ℝ) * (b + (d : ℝ)))) := by sorry

end IntegerRootsFN.Main
