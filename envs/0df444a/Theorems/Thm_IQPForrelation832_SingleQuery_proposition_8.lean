-- Prove2me | Theorems.Thm_IQPForrelation832_SingleQuery_proposition_8
-- name    : IQPForrelation832.SingleQuery.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T03:07:39.718623+00:00
-- url     : https://prove2.me/theorems/d5003cc0-9106-4073-8ec6-c82ea4c0fd2e
-- title:
--   Proposition 8 — randomized signed forrelation in even dimensions
-- statement:
--   There are two uniform efficient IQP circuit families, their common generator and an efficient branch-dependent accepting decider, all independent of the oracle truth tables, such that for every even natural dimension $n$ and arbitrary sign functions $f,g:V_n\to\{-1,1\}$, a fair choice of branch satisfies
--   $$
--   P_{\rm acc}=\frac12+\frac{\Phi(f,g)}{4}.
--   $$
--   Each selected circuit has $n+2$ wires and exactly one joint phase-query gate. Both branches are bounded by an absolute polynomial, and the same fair bit selects the corresponding accepting set.
--
--   For even dimensions the oracle acts only on the selector and the original address; the last wire is a dummy wire on which it acts as the identity. Dimension zero is included. This is the full signed-bias assertion in the indicated parity regime, with operational Born probabilities and no promise.
--
--   Differences from the source:
--   - reading: an efficient IQP procedure for arbitrary sign functions → one oracle-independent polynomial-time generator and accepting machine fixed before all dimensions and sign functions; reason: this implements the uniform preprocessing and efficient membership convention of Definition 4; PolyTimeComputable uses actual finite-machine semantics
--   - encoding: the constructive circuits in the proof with computational-basis measurement → fixed Z/CZ/query instruction parser, embedded joint oracle, two complete Hadamard layers and an unrenormalized Born sum; reason: the proof uses only these non-oracle middle gates; this witness gate set does not restrict generic IQP circuits and prevents arbitrary decoder or probability-oracle shortcuts
--   - encoding: binary strings and real sign-valued functions → Cube n = Fin n → ZMod 2 and real functions with an explicit IsSign predicate; reason: the coordinatewise Bool equivalence preserves every string, XOR, pairing and sign value, including dimension zero
--   - encoding: the proof uses one-bit padding and the original oracle → an explicit width n+2 and a query on the first n+1 wires; reason: this records the actual constructive witness; the dummy wire, when present, is untouched by the oracle
-- source:
--   Quentin Buzet, André Chailloux, IQP circuits for 2-Forrelation, STOC 2027 submission #832 (October 2026), p. 20, Proposition 8. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/832.pdf

import Definitions.Def_IQPForrelation832_SingleQuery_Programs

set_option autoImplicit false

namespace IQPForrelation832.SingleQuery

theorem proposition_8 :
    ∃ (p : ℕ → Bool → Program) (a : QAlgorithms.Complexity.Str → QAlgorithms.Complexity.Str),
      EfficientOn Even p a ∧
      ∀ n, Even n → (∀ b, (p n b).wires = n+2) ∧
        ∀ f g : Cube n → ℝ, IsSign f → IsSign g →
          fairBorn n p a f g = 1/2 + Phi f g / 4 := by sorry

end IQPForrelation832.SingleQuery
