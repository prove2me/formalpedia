-- Prove2me | Theorems.Thm_MantriCVQ_claim_7_2
-- name    : MantriCVQ.claim_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:10:19.866653+00:00
-- url     : https://prove2.me/theorems/135a7806-b7b1-49a0-a4fd-08bece24149e
-- title:
--   Claim 7.2 — a circuit for the machine with alternating quantifiers
-- statement:
--   Fix a deterministic oracle machine $V$, $k$ alternating quantifiers over strings of lengths $p_1(n),\dots,p_k(n)$ with either starting quantifier, a polynomial time bound $T$, and the oracle answers on all strings other than the leaves. The acceptance of $V$ on $1^n$ is computed on the leaves by a circuit of depth at most $k+2$ and size at most
--   $$O\bigl((k+T(n)+1)\,2^{p_1(n)+\cdots+p_k(n)+T(n)}\bigr)=2^{\mathrm{poly}(n)},$$
--   for a polynomial in the exponent that depends only on $V$. This reduces polynomial-hierarchy machines to the circuits of Theorem 1.7.
--
--   Differences from the source:
--   - generalization: the leaves of the instance of size n; T(n) bounds the time over all sequences of oracle answers → any finite set of oracle strings; T bounds the time on complete tuples for the oracles agreeing with O0 off the set; reason: the bound is needed only on consistent answers; the paper's case is an instance
--   - reading: the O(·) in the size bound → one absolute constant c chosen before V, k, the lengths and T; reason: the stronger reading; the proof's count gives an absolute constant
--   - encoding: a polynomial in the exponent that depends only on V → a polynomial r depending only on k, the lengths and T; reason: these are the only data the size bound involves
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Claim 7.2, p. 38 (PDF p. 40)

import Mathlib
import Definitions.Def_MantriCVQ_ACCircuit
import Definitions.Def_AvgPHETH_AltLen
import Definitions.Def_MantriCVQ_patch
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_tup

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ

/-- **Claim 7.2** (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Claim 7.2, p. 38 (PDF p. 40)): fix the oracle answers off the leaves. Then the acceptance of
`V` on `1^n` is computed on the leaves by a circuit of depth at most `k + 2` and size at most
`O((k + T(n) + 1) 2^{p₁(n)+⋯+p_k(n)+T(n)}) = 2^{poly(n)}`, for a polynomial in the exponent that depends only on `V`.

**Formalization Note** `O(·)` is one absolute constant `c`, chosen before everything else. The polynomial `r`
depends only on `k`, the `p_i` and `T`. The leaves are an arbitrary finite set `S` (a generalization), and `T` need
only bound the running time on the complete tuples for the oracles that agree with `O₀` off `S`. Both starting
quantifiers are covered, and `k = 0` is allowed. -/
theorem claim_7_2 : ∃ c : ℕ, ∀ (V : OTM) (k : ℕ) (ps : List (Polynomial ℕ)) (T : Polynomial ℕ),
    ps.length = k → ∃ r : Polynomial ℕ,
      (∀ n : ℕ, c * (k + T.eval n + 1) * 2 ^ ((ps.map fun p => p.eval n).sum + T.eval n) ≤
        2 ^ r.eval n) ∧
      ∀ (n : ℕ) (start : Bool) (O₀ : Oracle) (S : Finset Str),
        (∀ (ys : List Str) (a : S → Bool), ys.map List.length = ps.map (fun p => p.eval n) →
          (V.result (patch O₀ S a) (tup (unary n :: ys)) (T.eval n)).isSome) →
        ∃ F : ACCircuit S, F.depth ≤ k + 2 ∧
          F.size ≤ c * (k + T.eval n + 1) * 2 ^ ((ps.map fun p => p.eval n).sum + T.eval n) ∧
          ∀ a : S → Bool, F.eval a = true ↔
            AvgPHETH.AltLen (ps.map fun p => p.eval n) start
              (fun ys => V.result (patch O₀ S a) (tup (unary n :: ys)) (T.eval n) = some true) := by sorry

end MantriCVQ
