-- Prove2me | Theorems.Thm_IQPForrelation832_SingleQuery_Supplement_theorem_2
-- name    : IQPForrelation832.SingleQuery.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:54:45.285576+00:00
-- url     : https://prove2.me/theorems/97fa2e04-88ea-4074-b8f5-9c5cf6880be3
-- title:
--   Theorem 2 — squared forrelation from two queries
-- statement:
--   For every natural dimension $n$, including zero, and all sign functions $f,g:\{0,1\}^n\to\{-1,1\}$, there is one uniform randomized procedure whose two independently selected IQP runs make exactly two joint-oracle queries in total. It accepts exactly when the two decoded decision bits agree, with probability
--   $$
--   P_{\rm acc}(f,g)=
--   \begin{cases}\frac12+\frac14\Phi(f,g)^2,&n\text{ odd},\\
--   \frac12+\frac18\Phi(f,g)^2,&n\text{ even}.
--   \end{cases}
--   $$
--   Both branch coins and both quantum measurements are independent. No forrelation promise is imposed. The statement retains efficient generation and accepting deciders for the individual runs and validates their actual query counts. It is a companion to the retained one-query goal and makes the dependence insensitive to the sign of forrelation.
--
--   Differences from the source:
--   - encoding: run the randomized procedure twice independently and compare its outcomes → a tensor-product Born event averaged over the four equiprobable branch pairs; reason: this is precisely the finite joint distribution of the two independent executions; the published compiler and per-run efficiency predicate are unchanged
--   - reading: a randomized procedure using IQP circuits → one oracle-independent polynomial-time generator and accepting machine (the published EfficientOn) fixed before all dimensions and sign functions; reason: this is the uniform efficient-circuit convention of Definition 4, the same reading as the published goal; a uniform witness also witnesses the source's existence claim
--   - encoding: IQP circuits with computational-basis measurement → the published fixed Z/CZ/query instruction parser, embedded joint oracle, two Hadamard layers and an unrenormalized Born sum; reason: the proof only runs the circuits of Theorem 1, which use these gates; restricting the existential witness class does not weaken the statement
--   - encoding: binary strings and sign-valued functions → Cube n = Fin n → ZMod 2 and real functions with an explicit IsSign predicate; reason: the coordinatewise Bool equivalence preserves every string, pairing and sign value, including dimension zero
-- source:
--   Quentin Buzet, André Chailloux, IQP circuits for 2-Forrelation, STOC 2027 submission #832 (October 2026), p. 20, Theorem 2; proof pp. 21. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/832.pdf

import Definitions.Def_IQPForrelation832_SingleQuery_Supplement_Repetition

set_option autoImplicit false

namespace IQPForrelation832.SingleQuery.Supplement

open QAlgorithms QAlgorithms.Complexity

theorem theorem_2 :
    ∃ (p : ℕ → Bool → Program) (a : Str → Str),
      EfficientOn (fun _ => True) p a ∧
      ∀ n, TwoRunValid n p ∧
        ∀ f g : Cube n → ℝ, IsSign f → IsSign g →
          twoRunBorn n p a f g =
            (if Odd n then 1/2 + (Phi f g)^2 / 4 else 1/2 + (Phi f g)^2 / 8) := by sorry

end IQPForrelation832.SingleQuery.Supplement
