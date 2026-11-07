-- Prove2me | Theorems.Thm_KarpLiptonOM_lemma_A_3_9
-- name    : KarpLiptonOM.lemma_A_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:49:23.053449+00:00
-- url     : https://prove2.me/theorems/c53b7ff5-602e-45c7-bfe9-cc877b1271ea
-- title:
--   Lemma A.3.9 — canonical circuits from a tally language in PH
-- statement:
--   Assume $\mathrm{NP} \subseteq \mathrm{P/poly}$. Then for every $L \in \mathrm{PH}$ there is a tally language $T_L \in \mathrm{PH}$ such that $L \in \mathrm P^{T_L}$.
--
--   More precisely, there are a polynomial size bound $s$, with $\ell(n) = \ell(n, s(n))$ the length of the fixed encoding of circuits with $n$ inputs and at most $s(n)$ gates, and a polynomial-time oracle machine that, on input $1^n$ with oracle $T_L$,
--
--   1. asks exactly the queries $1^{\pi(n,1)}, 1^{\pi(n,2)}, \dots, 1^{\pi(n,\ell(n))}$, in this order, and
--   2. outputs the lexicographically first string of length $\ell(n)$ that encodes a circuit with $n$ inputs and at most $s(n)$ gates computing $L$ on $\{0,1\}^n$.
--
--   The canonical circuit is what makes the advice unique, which the transfer principle (Theorem A.3.10) and the unique-advice class OUM rely on.
--
--   Differences from the source:
--   - encoding: deterministic polynomial-time oracle machines with loose access to a promise oracle → OracleTM (work and query tape, one step per query, time |w|^k + k with every oracle), correct with every language consistent with the oracle, repeated queries allowed; reason: the paper's own form of loose access for deterministic machines (p.21); a standard machine model, polynomially equivalent to the others; the paper's assumption that machines never repeat a query (p.21) changes no class when the oracle is a fixed language
--   - encoding: binary strings, lengths polynomial in n (polynomials nondecreasing and at least 1, p.20), polynomial-time predicates on tuples → List Bool, lengths p.eval n for p : Polynomial ℕ (p ≥ 1 imposed only in L₂^P, OL₂^P and OMIN), predicates on u₁#⋯#u_k decided by the published CookPvsNP Turing machines; reason: Lean convention; same classes (a length polynomial with p(0) = 0 gives no new language or promise problem)
--   - reading: PH, Σ_k^P, NP and P/poly used without definition → PH = ⋃_{k≥1} Σ_k^P with Σ_k^P by alternating quantifiers; NP = CookPvsNP.NP Bool; P/poly in advice form; reason: standard definitions; P/poly in the paper's own form OGTD[poly, ∗, P] (p.24)
--   - reading: "a polynomial ℓ" and "the lexicographically first circuit of a fixed polynomial size" → a polynomial s, ℓ(n) = circuitLen n (s n) = ℓ(n, s(n)), and the lexicographically first code of length ℓ(n) of a circuit with at most s(n) gates computing L on {0,1}ⁿ; reason: the proof defines ℓ(n) = ℓ(n, s(n)) with s(n) = n^c + c; ℓ(n, s) = O(s log(n + s)) (p.20) is polynomially bounded
--   - encoding: the fixed encoding of circuits with n inputs and at most s gates by strings of length exactly ℓ(n, s) (p.20) → circuitCode / circuitLen: gate slots of 3 + 2·size(n+s) bits, empty slots zero; reason: the paper fixes an unspecified encoding with these properties; this is one
--   - encoding: "on input 1ⁿ, queries 1^π(n,1), …, 1^π(n,ℓ(n))" → the query trace within the time bound equals that list, in order; reason: the trace records every query of the run
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Lemma A.3.9, p.28

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_KarpLiptonOM_PH
import Definitions.Def_KarpLiptonOM_Ppoly
import Definitions.Def_KarpLiptonOM_IsTally
import Definitions.Def_KarpLiptonOM_InP
import Definitions.Def_KarpLiptonOM_toPromise
import Definitions.Def_KarpLiptonOM_OracleTM_trace
import Definitions.Def_KarpLiptonOM_OracleTM_init
import Definitions.Def_KarpLiptonOM_OracleTM_out
import Definitions.Def_KarpLiptonOM_IsLexFirstCircuit
import Definitions.Def_KarpLiptonOM_circuitLen
import Definitions.Def_KarpLiptonOM_cantor
import Definitions.Def_KarpLiptonOM_tupleEnc

namespace KarpLiptonOM

/-- Lemma A.3.9 (canonical circuits, p.28): if `NP ⊆ P/poly`, every `L ∈ PH` is in `P^{T_L}` for a tally `T_L ∈ PH`; more precisely, a polynomial-time oracle machine with oracle `T_L` on `1ⁿ` queries exactly `1^π(n,1), …, 1^π(n,ℓ(n))` and outputs the lexicographically first code of a circuit of a fixed polynomial size computing `L` on `{0,1}ⁿ`.

Source: Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b).

**Formalization Note** Strings, machines and classes are those of the `KarpLiptonOM` definitions: oracle access through every language consistent with the oracle, lengths `Polynomial ℕ`, polynomial-time predicates decided by the published `CookPvsNP` machines. The item's natural-language statement lists every difference from the page. -/
theorem lemma_A_3_9 (hNP : CookPvsNP.NP Bool ⊆ Ppoly) (L : Set (List Bool)) (hL : L ∈ PH) :
    ∃ T : Set (List Bool), IsTally T ∧ T ∈ PH ∧ InP (toPromise T) L ∧
      ∃ (s : Polynomial ℕ) (M : OracleTM) (k : ℕ), M.IsPolyTime k ∧ ∀ n : ℕ,
        M.trace T ((tupleEnc [List.replicate n true]).length ^ k + k)
            (M.init (tupleEnc [List.replicate n true])) =
          (List.range (circuitLen n (s.eval n))).map
            (fun i => List.replicate (cantor n (i + 1)) true) ∧
        IsLexFirstCircuit L n (s.eval n) (M.out T k (tupleEnc [List.replicate n true])) := by sorry

end KarpLiptonOM
