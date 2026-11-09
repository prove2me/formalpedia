-- Prove2me | Theorems.Thm_IQPForrelation832_SingleQuery_theorem_1
-- name    : IQPForrelation832.SingleQuery.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T03:07:33.332957+00:00
-- url     : https://prove2.me/theorems/c8c2ae8f-d9dc-4ca5-88bf-9c7de9426d79
-- title:
--   Theorem 1 — signed forrelation with one quantum query
-- statement:
--   There exist two uniform efficient IQP circuit families, one polynomial-time generator and one polynomial-time accepting decider, chosen before the dimension and before either oracle function. For every natural $n$, every $f,g:V_n\to\{-1,1\}$, and a fair classical choice between the two branches, the exact acceptance probability is
--   $$
--   P_{\rm acc}=\begin{cases}
--   \dfrac12+\dfrac{\Phi(f,g)}{2\sqrt2},&n\text{ odd},\\[3pt]
--   \dfrac12+\dfrac{\Phi(f,g)}4,&n\text{ even}.
--   \end{cases}
--   $$
--   Each chosen circuit has exactly one joint phase-query gate, polynomial total size including its two full Hadamard layers, and an efficiently decidable accepting set. The witnesses use $n+1$ wires when $n$ is odd and $n+2$ when $n$ is even; padding wires are untouched by the original oracle. Size bounds have absolute coefficients and degree outside the quantifier over $n$. Both classical machines have genuine finite-machine polynomial-time bounds on all inputs and receive no truth tables.
--
--   This is the paper's complete signed one-query target, with both parity cases and arbitrary sign functions. At $n=0$, $\Phi=fg$ and the probabilities are $3/4$ and $1/4$; no positive-dimension hypothesis is added.
--
--   Differences from the source:
--   - reading: an efficient IQP procedure for arbitrary sign functions → one oracle-independent polynomial-time generator and accepting machine fixed before all dimensions and sign functions; reason: this implements the uniform preprocessing and efficient membership convention of Definition 4; PolyTimeComputable uses actual finite-machine semantics
--   - encoding: the constructive circuits in the proof with computational-basis measurement → fixed Z/CZ/query instruction parser, embedded joint oracle, two complete Hadamard layers and an unrenormalized Born sum; reason: the proof uses only these non-oracle middle gates; this witness gate set does not restrict generic IQP circuits and prevents arbitrary decoder or probability-oracle shortcuts
--   - encoding: binary strings and real sign-valued functions → Cube n = Fin n → ZMod 2 and real functions with an explicit IsSign predicate; reason: the coordinatewise Bool equivalence preserves every string, XOR, pairing and sign value, including dimension zero
--   - encoding: the theorem has no width constraint, and its proof pads even dimensions → the constructive widths are n+1 for odd n and n+2 for even n; reason: these are the witnesses supplied by the proof; the introduction informal n+1 count is not imposed on even dimensions
-- source:
--   Quentin Buzet, André Chailloux, IQP circuits for 2-Forrelation, STOC 2027 submission #832 (October 2026), p. 6, Theorem 1; restatement p. 13; proof pp. 19–20. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/832.pdf

import Definitions.Def_IQPForrelation832_SingleQuery_Programs

set_option autoImplicit false

namespace IQPForrelation832.SingleQuery

theorem theorem_1 :
    ∃ (p : ℕ → Bool → Program) (a : QAlgorithms.Complexity.Str → QAlgorithms.Complexity.Str),
      EfficientOn (fun _ => True) p a ∧
      ∀ n, (∀ b, (p n b).wires = (if Odd n then n+1 else n+2)) ∧
        ∀ f g : Cube n → ℝ, IsSign f → IsSign g →
          fairBorn n p a f g =
            (if Odd n then 1/2 + Phi f g / (2 * Real.sqrt 2) else 1/2 + Phi f g / 4) := by sorry

end IQPForrelation832.SingleQuery
