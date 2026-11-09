-- Prove2me | Theorems.Thm_IQPForrelation832_SingleQuery_proposition_1
-- name    : IQPForrelation832.SingleQuery.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T03:07:23.732533+00:00
-- url     : https://prove2.me/theorems/e9879733-4744-4a02-b12c-65f541364018
-- title:
--   Proposition 1 — IQP acceptance from supplied phase functions
-- statement:
--   For each natural dimension $n$, let $\rho_{0,n},\rho_{1,n}:V_n\to\{-1,1\}$ and $\sigma_n:V_n\to\mathbb R$. Suppose supplied polynomial-size computational-basis diagonal unitary gate lists implement the selector-diagonal operator with phases $\rho_{0,n}$ and $\rho_{1,n}$. The gates have an absolute locality bound; the implementations need not have a uniform generator. Suppose also that the orthonormal transform $\widehat\sigma_n$ takes values in $\{-1,1\}$ and one classical polynomial-time algorithm computes those sign bits.
--
--   There is one polynomial-time accepting decider and an absolute polynomial size bound such that, for every $n$ and every pair of sign functions $f,g:V_n\to\{-1,1\}$, the IQP circuit retaining the supplied implementation and making one joint query satisfies
--   $$
--   P_{\rm acc}=\frac12+\sqrt{\frac1{2^{3n+2}}}\sum_{x,y\in V_n}f(x)g(y)\rho_{0,n}(x)\rho_{1,n}(y)\sigma_n(x+y).
--   $$
--   The statement concludes the acceptance identity and the resource guarantees; neither is built into the definition of a circuit. The proof's sign error in its accepting-set witness is repaired by using $F=(\{0\}\times T)\cup(\{1\}\times T^{\rm c})$ for $T=\{x:\widehat\sigma_n(x)=1\}$. The proposition's assertion and positive coefficient are unchanged.
--
--   Differences from the source:
--   - reading: polynomial-size diagonal implementation and efficiently computable sign-valued transform → families of supplied bounded-locality diagonal unitary gate lists with absolute polynomial size and one polynomial-time transform transducer; reason: efficiency is a uniform-in-length assertion; the elementary-gate locality bound excludes unit-cost arbitrary dense matrices, permits any fixed locality and gate library, and adds no generator requirement to the supplied implementations
--   - encoding: the circuit of Figure 6 and efficient accepting-set membership → the original supplied gate list with one prepended joint query, actual Born probability, and a finite-machine decider on a fixed self-delimiting encoding; reason: the implementation is retained exactly and its probability is concluded; no truth table is a classical input and no acceptance formula is assumed
--   - encoding: binary strings and real sign-valued functions → Cube n = Fin n → ZMod 2 and real functions with an explicit IsSign predicate; reason: the coordinatewise Bool equivalence preserves every string, XOR, pairing and sign value, including dimension zero
-- source:
--   Quentin Buzet, André Chailloux, IQP circuits for 2-Forrelation, STOC 2027 submission #832 (October 2026), pp. 14–15, Proposition 1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/832.pdf

import Definitions.Def_IQPForrelation832_SingleQuery_Programs

set_option autoImplicit false

namespace IQPForrelation832.SingleQuery

/-- Generic supplied implementations need polynomial size, not a uniform generator.
The output retains these very implementations and uses a uniform accepting decider. -/
theorem proposition_1
    (r0 r1 sigma : ∀ n, Cube n → ℝ)
    (impl : ∀ n, QAlgorithms.Circuit Set.univ (n+1))
    (hr0 : ∀ n, IsSign (r0 n)) (hr1 : ∀ n, IsSign (r1 n))
    (hsize : PolynomialImplementation impl)
    (himpl : ∀ n, QAlgorithms.Circuit.unitary (impl n) = phaseDiagonal (r0 n) (r1 n))
    (hbent : ∀ n, IsSign (realFourier (sigma n)))
    (hcompute : ComputableTransform sigma) :
    ∃ a : QAlgorithms.Complexity.Str → QAlgorithms.Complexity.Str,
      QAlgorithms.Complexity.PolyTimeComputable a ∧
      ∃ C d : ℕ, ∀ n,
        IsIQP (withQuery (impl n)) ∧
        QAlgorithms.OracleCircuit.queryCount (withQuery (impl n)) 0 = 1 ∧
        (withQuery (impl n)).length + 2*(n+1) ≤ C*(n+1)^d ∧
        ∀ f g : Cube n → ℝ, IsSign f → IsSign g →
          born (withQuery (impl n)) (accepts a n false) f g =
            1/2 + Real.sqrt (1 / (2 : ℝ)^(3*n+2)) *
              ∑ x, ∑ y, f x * g y * r0 n x * r1 n y * sigma n (x+y) := by sorry

end IQPForrelation832.SingleQuery
