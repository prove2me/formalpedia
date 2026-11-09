-- Prove2me | Theorems.Thm_IQPForrelation832_SingleQuery_proposition_5
-- name    : IQPForrelation832.SingleQuery.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T03:07:37.171058+00:00
-- url     : https://prove2.me/theorems/40aa4d04-9582-44b6-b5a2-747dbc6d3fb1
-- title:
--   Proposition 5 — one query for odd parity forrelation
-- statement:
--   There is a uniform family of efficient IQP circuits and an efficient accepting-set decider, fixed independently of $f,g$, such that for every odd natural dimension $n$ and arbitrary sign functions $f,g:V_n\to\{-1,1\}$,
--   $$
--   P_{\rm acc}=\frac12+\frac{\Phi_{\rm odd}(f,g)}{\sqrt2}.
--   $$
--   Here $\Phi_{\rm odd}$ is the normalized forrelation sum restricted to pairs with $|x+y|$ odd. Each circuit uses $n+1$ wires and exactly one occurrence of the joint oracle. The circuit description, including the two outer Hadamard layers, has one absolute polynomial bound over all odd dimensions.
--
--   The single circuit may be regarded as a family with an ignored branch bit in its generator interface; its probability is evaluated at the fixed branch zero. No input promise on forrelation is assumed. This is the odd-parity component of the signed one-query assertion.
--
--   Differences from the source:
--   - reading: an efficient IQP procedure for arbitrary sign functions → one oracle-independent polynomial-time generator and accepting machine fixed before all dimensions and sign functions; reason: this implements the uniform preprocessing and efficient membership convention of Definition 4; PolyTimeComputable uses actual finite-machine semantics
--   - encoding: the constructive circuits in the proof with computational-basis measurement → fixed Z/CZ/query instruction parser, embedded joint oracle, two complete Hadamard layers and an unrenormalized Born sum; reason: the proof uses only these non-oracle middle gates; this witness gate set does not restrict generic IQP circuits and prevents arbitrary decoder or probability-oracle shortcuts
--   - encoding: binary strings and real sign-valued functions → Cube n = Fin n → ZMod 2 and real functions with an explicit IsSign predicate; reason: the coordinatewise Bool equivalence preserves every string, XOR, pairing and sign value, including dimension zero
-- source:
--   Quentin Buzet, André Chailloux, IQP circuits for 2-Forrelation, STOC 2027 submission #832 (October 2026), p. 17, Proposition 5 (calculation continues p. 18). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/832.pdf

import Definitions.Def_IQPForrelation832_SingleQuery_Programs

set_option autoImplicit false

namespace IQPForrelation832.SingleQuery

theorem proposition_5 :
    ∃ (p : ℕ → Program) (a : QAlgorithms.Complexity.Str → QAlgorithms.Complexity.Str),
      EfficientOn Odd (fun n _ => p n) a ∧
      ∀ n, Odd n → (p n).wires = n+1 ∧
        ∀ f g : Cube n → ℝ, IsSign f → IsSign g →
          programBorn n (p n) a false f g = 1/2 + parityPhi true f g / Real.sqrt 2 := by sorry

end IQPForrelation832.SingleQuery
