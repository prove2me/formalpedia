-- Prove2me | Theorems.Thm_KarpLiptonOM_lemma_A_4_1
-- name    : KarpLiptonOM.lemma_A_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:48:56.529093+00:00
-- url     : https://prove2.me/theorems/3e0cecb7-5e03-4e58-8fba-2a902e8fa63e
-- title:
--   Lemma A.4.1 — sampling sOprMA oracles with an ONP oracle; $\mathrm P^{\mathrm{sOprMA}}\subseteq\mathrm{BPP}^{\mathrm{ONP}}$
-- statement:
--   For every $\Pi \in \mathrm{sOprMA}$ there is a language $K_\Pi \in \mathrm{ONP}$ with the following property. For every deterministic polynomial-time oracle transducer $M$ there is a randomized polynomial-time oracle transducer $M'$ such that for every input $z$,
--   $$
--   \Pr_r\Bigl[\, M'^{K_\Pi}(z, r) = M^O(z) \text{ for some language } O \text{ consistent with } \Pi \Bigr] \ge \tfrac34 .
--   $$
--   In particular, $\mathrm P^{\mathrm{sOprMA}} \subseteq \mathrm{BPP}^{\mathrm{ONP}}$.
--
--   The pointwise domination condition (OMA4) is what makes the sampling work; the lemma is applied to generators in the proof that $\mathrm{OM} \subseteq \mathrm{ZPP}^{\mathrm{ONP}}$.
--
--   Differences from the source:
--   - encoding: deterministic polynomial-time oracle machines with loose access to a promise oracle → OracleTM (work and query tape, one step per query, time |w|^k + k with every oracle), correct with every language consistent with the oracle, repeated queries allowed; reason: the paper's own form of loose access for deterministic machines (p.21); a standard machine model, polynomially equivalent to the others; the paper's assumption that machines never repeat a query (p.21) changes no class when the oracle is a fixed language
--   - encoding: binary strings, lengths polynomial in n (polynomials nondecreasing and at least 1, p.20), polynomial-time predicates on tuples → List Bool, lengths p.eval n for p : Polynomial ℕ (p ≥ 1 imposed only in L₂^P, OL₂^P and OMIN), predicates on u₁#⋯#u_k decided by the published CookPvsNP Turing machines; reason: Lean convention; same classes (a length polynomial with p(0) = 0 gives no new language or promise problem)
--   - reading: BPP^ONP used without definition → standard BPP with error at most 1/3; reason: standard definition; Lemma A.4.1 gives success probability 3/4
--   - encoding: a randomized transducer M′ on input z, probability over its coins → a deterministic transducer M′ on (z, r), r uniform over {0,1}^{q(|z|)}; probability ≥ 3/4 as 4·#{r} ≥ 3·2^{q(|z|)}; reason: random strings as a second input of polynomial length (p.20)
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Lemma A.4.1, p.29

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_KarpLiptonOM_sOprMA
import Definitions.Def_KarpLiptonOM_ONP
import Definitions.Def_KarpLiptonOM_OracleTM_IsPolyTime
import Definitions.Def_KarpLiptonOM_OracleTM_out
import Definitions.Def_KarpLiptonOM_Consistent
import Definitions.Def_KarpLiptonOM_countStr
import Definitions.Def_KarpLiptonOM_PC
import Definitions.Def_KarpLiptonOM_BPP
import Definitions.Def_KarpLiptonOM_tupleEnc

namespace KarpLiptonOM

/-- Lemma A.4.1 (sampling sOprMA oracles, p.29): for every `Π ∈ sOprMA` there is `K_Π ∈ ONP` such that every polynomial-time oracle transducer `M` has a randomized polynomial-time oracle transducer `M′` with `Pr_r[M′^{K_Π}(z, r) = M^O(z) for some O consistent with Π] ≥ 3/4` for every `z`; in particular `P^sOprMA ⊆ BPP^ONP`.

Source: Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b).

**Formalization Note** Strings, machines and classes are those of the `KarpLiptonOM` definitions: oracle access through every language consistent with the oracle, lengths `Polynomial ℕ`, polynomial-time predicates decided by the published `CookPvsNP` machines. The item's natural-language statement lists every difference from the page. -/
theorem lemma_A_4_1 :
    (∀ PP : PromiseProblem, sOprMA PP → ∃ K ∈ ONP, ∀ (M : OracleTM) (k : ℕ), M.IsPolyTime k →
      ∃ (M' : OracleTM) (k' : ℕ) (q : Polynomial ℕ), M'.IsPolyTime k' ∧ ∀ z : List Bool,
        3 * 2 ^ q.eval z.length ≤ 4 * countStr (q.eval z.length) (fun r =>
          ∃ O, Consistent O PP ∧ M'.out K k' (tupleEnc [z, r]) = M.out O k (tupleEnc [z]))) ∧
    PC {PP | sOprMA PP} ⊆ {L | ∃ A ∈ ONP, BPP A L} := by sorry

end KarpLiptonOM
