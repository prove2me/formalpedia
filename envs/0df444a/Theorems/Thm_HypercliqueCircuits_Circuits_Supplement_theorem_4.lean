-- Prove2me | Theorems.Thm_HypercliqueCircuits_Circuits_Supplement_theorem_4
-- name    : HypercliqueCircuits.Circuits.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:13:34.618697+00:00
-- url     : https://prove2.me/theorems/1f4c703d-066b-4434-894e-ddc834983a7a
-- title:
--   Theorem 4 — optimal assignments for Max-Degree-kCSP
-- statement:
--   Fix $k\ge3$. There are $\delta_k,C_k>0$, a natural exponent $c_k$, and one algorithm that, for every $n,m\ge0$ and every valid family $F$ of $m$ degree-at-most-$k$ Boolean constraints on $n$ variables, outputs an assignment $x\in\{0,1\}^n$ satisfying
--
--   $$\#\{i:F_i(x)=1\}\ge\#\{i:F_i(y)=1\}\quad\text{for every }y\in\{0,1\}^n,$$
--
--   with bit cost at most
--
--   $$C_k 2^{(1-\delta_k)n}(n+m+2)^{c_k}.$$
--
--   Every constraint is supplied by its exact sparse multilinear polynomial in the Boolean monomial basis, not by a truth table. A degree-$k$ constraint may depend on more than $k$ variables. Repeated constraints, no constraints, and no variables are included. The program, saving, multiplicative constant and polynomial exponent are fixed before $n,m$ and the instance. This is the full optimization application, requiring an assignment rather than only the optimum value.
--
--   Differences from the source:
--   - reading: algorithmic running time without an explicit instruction set → a finite Program Empty with actual halting execution and the published executionBits cost; reason: the supplement inherits the live mission machine; arithmetic, accessed-word lengths, and output serialization are charged, and no oracle instruction can be instantiated
--   - encoding: degree-at-most-k Boolean functions in their unique multilinear representation → lists of distinct squarefree monomials with nonzero integer coefficients, increasing variable indices, degree at most k, and Boolean values on the entire cube; reason: Möbius inversion gives integral coefficients for every Boolean function; this imposes no arity restriction or loss of degree-k constraints
--   - encoding: m constraints and an optimal Boolean assignment → a Fin m-indexed family, length-prefixed signed polynomial data, and n output bits maximizing satisfiedCount; reason: indexing permits repeated constraints and the empty family; the output retains the requested assignment
--   - encoding: 2^((1−δ_k)n) poly(n,m) → C_k times 2^((1−δ_k)n) times (n+m+2)^c_k for all n,m including zero; reason: one fixed polynomial in two nonnegative sizes is bounded by this form; the shift makes the bound nonzero at empty sizes
-- source:
--   Josh Alman, Baitian Li, Neha Pant, Kevin Pratt, Ryan Williams, Finding Hypercliques Faster Than Brute Force, STOC 2027 submission #1224 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1224.pdf, p.2, Theorem 4 (PDF 3); proof p.26 (PDF 27)

import Definitions.Def_HypercliqueCircuits_Circuits_Supplement_DegreeCSP

set_option autoImplicit false

namespace HypercliqueCircuits.Circuits.Supplement

/-- Theorem 4, printed p.2 (proof p.26), PDF p.3 (proof p.27).
The algorithm returns an optimal ASSIGNMENT on every valid instance,
including repeated constraints, m = 0, and n = 0. -/
theorem theorem_4 (k : ℕ) (hk : 3 ≤ k) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∃ c : ℕ, ∃ prog : Program Empty,
      ∀ n m : ℕ, ∀ F : CSPInstance n m, ValidCSP k F →
        ∃ t : ℕ, ∃ x : Fin n → Bool,
          (execute prog (cspInput F) t).halted = true ∧
          (execute prog (cspInput F) t).output = assignmentWords x ∧
          (∀ y : Fin n → Bool, satisfiedCount F y ≤ satisfiedCount F x) ∧
          (executionBits Empty.elim prog (cspInput F) t : ℝ) ≤
            C * (2 : ℝ) ^ ((1 - δ) * (n : ℝ)) * ((n + m + 2 : ℕ) : ℝ) ^ c := by sorry

end HypercliqueCircuits.Circuits.Supplement
