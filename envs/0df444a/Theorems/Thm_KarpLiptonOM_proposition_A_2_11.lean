-- Prove2me | Theorems.Thm_KarpLiptonOM_proposition_A_2_11
-- name    : KarpLiptonOM.proposition_A_2_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:48:10.748188+00:00
-- url     : https://prove2.me/theorems/d467c53e-8fe7-4ec3-8453-9900a3e07ff6
-- title:
--   Proposition A.2.11 — basic properties of $\mathrm{OGTD}[\Pi]$
-- statement:
--   Let $\Pi, \Pi', \Pi_1, \dots, \Pi_r$ be promise problems, and write $\mathrm{OGTD}[\Pi] = \mathrm{OGTD}[\mathrm{FP}^\Pi, *, \mathrm P]$ for the languages with polynomial-size advice computable from $1^n$ in $\mathrm{FP}^\Pi$.
--
--   1. $\mathrm{OGTD}[\Pi] \subseteq \mathrm P^\Pi \cap \mathrm{P/poly}$, and $\mathrm{OGTD}[\Pi]$ is closed under complement.
--   2. If $\Pi = A$ is a language, then $\mathrm{OGTD}[A] = \mathrm P^{\mathrm{TALLY} \cap \mathrm P^A}$, i.e. $L \in \mathrm{OGTD}[A]$ iff $L \in \mathrm P^T$ for some tally language $T \in \mathrm P^A$.
--   3. If $L \in \mathrm P^{L_1, \dots, L_r}$ and $L_i \in \mathrm{OGTD}[\Pi_i]$ for all $i$, then $L \in \mathrm{OGTD}[\Pi_1 \oplus \cdots \oplus \Pi_r]$. In particular, $\mathrm P^{\mathrm{OGTD}[\Pi]} = \mathrm{OGTD}[\Pi]$.
--   4. Suppose some deterministic polynomial-time oracle machine $M$ has the property that for every language $O$ consistent with $\Pi$ the language decided by $M^O$ is consistent with $\Pi'$. Then
--   $$
--   \mathrm{OGTD}[\Pi'] \subseteq \mathrm{OGTD}[\Pi], \qquad \mathrm P^{\Pi'} \subseteq \mathrm P^{\Pi}, \qquad \mathrm{FP}^{\Pi'} \subseteq \mathrm{FP}^{\Pi}.
--   $$
--
--   These closure properties let the paper move between oracles: part 2 is the tally characterization behind the collapse to OMIN, part 3 closes OGTD classes under Turing reductions, and part 4 replaces one oracle by another that simulates it.
--
--   Differences from the source:
--   - encoding: deterministic polynomial-time oracle machines with loose access to a promise oracle → OracleTM (work and query tape, one step per query, time |w|^k + k with every oracle), correct with every language consistent with the oracle, repeated queries allowed; reason: the paper's own form of loose access for deterministic machines (p.21); a standard machine model, polynomially equivalent to the others; the paper's assumption that machines never repeat a query (p.21) changes no class when the oracle is a fixed language
--   - encoding: binary strings, lengths polynomial in n (polynomials nondecreasing and at least 1, p.20), polynomial-time predicates on tuples → List Bool, lengths p.eval n for p : Polynomial ℕ (p ≥ 1 imposed only in L₂^P, OL₂^P and OMIN), predicates on u₁#⋯#u_k decided by the published CookPvsNP Turing machines; reason: Lean convention; same classes (a length polynomial with p(0) = 0 gives no new language or promise problem)
--   - generalization: promise problems Π₁, …, Π_r in (c), r ≥ 1 implicitly → every r ∈ ℕ, including r = 0 (the join of no problems is (∅, ∅), and P^{L₁,…,L_r} is P); reason: the r = 0 case also holds (a polynomial-time language is decided with empty advice); the statement specializes to every printed r ≥ 1
--   - encoding: P^{L₁,…,L_r} (several oracles); Π₁⊕⋯⊕Π_r with i written in a fixed number of bits → P with the single oracle L₁⊕⋯⊕L_r (langJoin); the tag of i is its one-hot code of width r; reason: the identification the paper itself uses (p.21, proof of Lemma A.3.1); any fixed-width code gives the same classes
--   - encoding: P^{OGTD[Π]} (P with an oracle from the class OGTD[Π]) → {L | ∃ A ∈ OGTD[Π], L ∈ P^A}; reason: P^C for a class of languages is the union over its members (Definition A.2.1)
--   - encoding: P/poly → Ppoly (advice form); reason: the paper's own definition P/poly = OGTD[poly, ∗, P], p.24
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Proposition A.2.11, p.24

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_KarpLiptonOM_OGTD
import Definitions.Def_KarpLiptonOM_InP
import Definitions.Def_KarpLiptonOM_InFP
import Definitions.Def_KarpLiptonOM_Ppoly
import Definitions.Def_KarpLiptonOM_IsTally
import Definitions.Def_KarpLiptonOM_toPromise
import Definitions.Def_KarpLiptonOM_Consistent
import Definitions.Def_KarpLiptonOM_langJoin
import Definitions.Def_KarpLiptonOM_promiseJoin
import Definitions.Def_KarpLiptonOM_OracleTM_Accepts
import Definitions.Def_KarpLiptonOM_tupleEnc

namespace KarpLiptonOM

/-- Proposition A.2.11 (p.24): (a) `OGTD[Π] ⊆ P^Π ∩ P/poly` and `OGTD[Π]` is closed under complement; (b) `OGTD[A] = P^{TALLY ∩ P^A}` for a language `A`; (c) `L ∈ P^{L₁,…,L_r}`, `Lᵢ ∈ OGTD[Πᵢ]` ⇒ `L ∈ OGTD[Π₁⊕⋯⊕Π_r]`, and `P^{OGTD[Π]} = OGTD[Π]`; (d) a polynomial-time `M` turning every oracle consistent with `Π` into a language consistent with `Π'` gives `OGTD[Π'] ⊆ OGTD[Π]`, `P^{Π'} ⊆ P^Π`, `FP^{Π'} ⊆ FP^Π`.

Source: Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b).

**Formalization Note** Strings, machines and classes are those of the `KarpLiptonOM` definitions: oracle access through every language consistent with the oracle, lengths `Polynomial ℕ`, polynomial-time predicates decided by the published `CookPvsNP` machines. The item's natural-language statement lists every difference from the page. -/
theorem proposition_A_2_11 :
    (∀ PP : PromiseProblem,
      OGTD {PP} Set.univ ⊆ {L | InP PP L} ∩ Ppoly ∧
      ∀ L ∈ OGTD {PP} Set.univ, Lᶜ ∈ OGTD {PP} Set.univ) ∧
    (∀ A : Set (List Bool), OGTD {toPromise A} Set.univ =
      {L | ∃ T : Set (List Bool), IsTally T ∧ InP (toPromise A) T ∧ InP (toPromise T) L}) ∧
    (∀ (r : ℕ) (PP : Fin r → PromiseProblem) (Ls : Fin r → Set (List Bool)) (L : Set (List Bool)),
      InP (toPromise (langJoin Ls)) L → (∀ i, Ls i ∈ OGTD {PP i} Set.univ) →
        L ∈ OGTD {promiseJoin PP} Set.univ) ∧
    (∀ PP : PromiseProblem,
      {L | ∃ A ∈ OGTD {PP} Set.univ, InP (toPromise A) L} = OGTD {PP} Set.univ) ∧
    (∀ PP PP' : PromiseProblem,
      (∃ (M : OracleTM) (k : ℕ), M.IsPolyTime k ∧
        ∀ O, Consistent O PP → Consistent {q | M.Accepts O (tupleEnc [q])} PP') →
      OGTD {PP'} Set.univ ⊆ OGTD {PP} Set.univ ∧ (∀ L, InP PP' L → InP PP L) ∧
        (∀ R : List Bool → List Bool → Prop, InFP PP' R → InFP PP R)) := by sorry

end KarpLiptonOM
