-- Prove2me | Theorems.Thm_KarpLiptonOM_facts_F1_F2
-- name    : KarpLiptonOM.facts_F1_F2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:42:45.170677+00:00
-- url     : https://prove2.me/theorems/9e8252db-c2a5-4e61-9a7b-94600650e264
-- title:
--   Facts (F1), (F2) (cited, [KP24], [HVW26]) — $\mathrm{NP\subseteq L_2^P}$, $\mathrm{OL_2^P=OMIN\subseteq O_2^P}$, $\mathrm{OL_2^P}\not\subseteq\mathrm{SIZE}[n^k]$
-- statement:
--   The known facts (F1) and (F2), cited from Korten–Pitassi [KP24] and Hirsch–Volkovich–Wang [HVW26]:
--
--   1. (F1) $\mathrm{NP} \subseteq \mathrm L^{\mathrm P}_2$;
--   2. (F2) $\mathrm{OL}^{\mathrm P}_2 = \mathrm{OMIN}$, and $\mathrm{OL}^{\mathrm P}_2 \not\subseteq \mathrm{SIZE}[n^k]$ for every $k$;
--   3. $\mathrm{OL}^{\mathrm P}_2 \subseteq \mathrm L^{\mathrm P}_2$;
--   4. $\mathrm{OMIN} \subseteq \mathrm O^{\mathrm P}_2$.
--
--   They place the linear-order classes in the landscape: OMIN and $\mathrm{OL}^{\mathrm P}_2$ are the same class, it sits inside $\mathrm L^{\mathrm P}_2$ and $\mathrm O^{\mathrm P}_2$, and it has no fixed-polynomial-size circuits.
--
--   Differences from the source:
--   - encoding: binary strings, lengths polynomial in n (polynomials nondecreasing and at least 1, p.20), polynomial-time predicates on tuples → List Bool, lengths p.eval n for p : Polynomial ℕ (p ≥ 1 imposed only in L₂^P, OL₂^P and OMIN), predicates on u₁#⋯#u_k decided by the published CookPvsNP Turing machines; reason: Lean convention; same classes (a length polynomial with p(0) = 0 gives no new language or promise problem)
--   - reading: (F1) NP ⊆ L₂^P, "with an explicit linear order for every NP verifier [HVW26, Lemma 2.11]" → NP ⊆ L₂^P; reason: the clause says how the containment is witnessed (where an explicit order is given); the containment is its mathematical content
--   - reading: SIZE[n^k] used without definition → SIZE k: circuits with at most c·n^k + c gates for a constant c; reason: standard class; quantified over every k, size O(n^k) and size n^k give the same statement
--   - encoding: NP → CookPvsNP.NP Bool (witnesses of length ≤ |w|^k); reason: the published Cook definition; the same class as NP with witnesses of exact polynomial length
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Facts (F1) and (F2), p.23 (cited: [KP24]; [HVW26, Theorems 3.3, 3.4, Lemma 2.11])

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_KarpLiptonOM_LP2
import Definitions.Def_KarpLiptonOM_OLP2
import Definitions.Def_KarpLiptonOM_OMIN
import Definitions.Def_KarpLiptonOM_OP2
import Definitions.Def_KarpLiptonOM_SIZE

namespace KarpLiptonOM

/-- Facts (F1) and (F2) (p.23; cited from [KP24] and [HVW26, Theorems 3.3, 3.4]): `NP ⊆ L₂^P`, `OL₂^P = OMIN`, `OL₂^P ⊄ SIZE[n^k]` for every `k`, `OL₂^P ⊆ L₂^P`, and `OMIN ⊆ O₂^P`.

Source: Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b).

**Formalization Note** Strings, machines and classes are those of the `KarpLiptonOM` definitions: oracle access through every language consistent with the oracle, lengths `Polynomial ℕ`, polynomial-time predicates decided by the published `CookPvsNP` machines. The item's natural-language statement lists every difference from the page. -/
theorem facts_F1_F2 :
    CookPvsNP.NP Bool ⊆ LP2 ∧ OLP2 = OMIN ∧ (∀ k : ℕ, ¬ OLP2 ⊆ SIZE k) ∧ OLP2 ⊆ LP2 ∧
      OMIN ⊆ OP2 := by sorry

end KarpLiptonOM
