-- Prove2me | Theorems.Thm_MantriCVQ_claim_7_1
-- name    : MantriCVQ.claim_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:10:22.157628+00:00
-- url     : https://prove2.me/theorems/7c31db17-dfbb-4d6e-a6dd-8f3c6a08bad2
-- title:
--   Claim 7.1 — a DNF for one complete tuple
-- statement:
--   Fix a deterministic oracle machine $V$, an input (in the paper, $1^n$ and a complete tuple $(y_1,\dots,y_k)$) and the oracle answers on all strings other than a finite set of leaves. If $V$ halts within $T$ steps for every answer on the leaves, there is a DNF of width at most $T$ with at most $2^T$ terms over the leaves that agrees with $V^O$ on every leaf table, valid or not. This is the bottom layer of the circuit of Claim 7.2.
--
--   Differences from the source:
--   - generalization: input 1^n with a complete tuple; the leaves of the instance of size n; T(n) bounds the time over all sequences of oracle answers → any input string, any finite set of oracle strings; T bounds the time for the oracles agreeing with O0 off the set; reason: the bound is needed only on consistent answers; the paper's case is an instance
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Claim 7.1, p. 38 (PDF p. 40)

import Mathlib
import Definitions.Def_MantriCVQ_listWidth
import Definitions.Def_MantriCVQ_patch
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_SamplingAC0_DNF

open QAlgorithms.Complexity QAdvFew.PoQOracle SamplingAC0

namespace MantriCVQ

/-- **Claim 7.1** (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Claim 7.1, p. 38 (PDF p. 40)): fix the input (`1^n` and a complete tuple) and the oracle
answers off the leaves. Then there is a DNF of width at most `T` with at most `2^T` terms over the leaves that
agrees with the machine on every leaf table, valid or not.

**Formalization Note** The input is an arbitrary string `s` and the leaves are an arbitrary finite set `S` of
strings (a generalization); the paper's case is `s = tup (1^n, y₁, …, y_k)` and `S` the leaf addresses of the
instance of size `n`. The bound `T` need only hold for the oracles that agree with `O₀` off `S`. -/
theorem claim_7_1 (V : OTM) (s : Str) (O₀ : Oracle) (S : Finset Str) (T : ℕ)
    (hT : ∀ a : S → Bool, (V.result (patch O₀ S a) s T).isSome) :
    ∃ φ : DNF S, listWidth φ ≤ T ∧ φ.length ≤ 2 ^ T ∧
      ∀ a : S → Bool, DNF.eval φ a = true ↔ V.result (patch O₀ S a) s T = some true := by sorry

end MantriCVQ
