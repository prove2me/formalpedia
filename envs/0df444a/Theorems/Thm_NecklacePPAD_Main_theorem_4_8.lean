-- Prove2me | Theorems.Thm_NecklacePPAD_Main_theorem_4_8
-- name    : NecklacePPAD.Main.theorem_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:09:57.800908+00:00
-- url     : https://prove2.me/theorems/1fa7190b-80ea-4856-85d5-fe0d37f1ea89
-- title:
--   Theorem 4.8 — for half-sizes ≥ (5, 4, 3) the construction is a polynomial-time reduction from Pure-Circuit to Necklace-Splitting
-- statement:
--   For all half-sizes $b_{\rm NOR}\ge5$, $b_{\rm NP}\ge4$, $b_{\rm NOT}\ge3$, the construction is a polynomial-time reduction from Pure-Circuit to Necklace-Splitting: (i) for every Pure-Circuit instance, every choice of orders and every split $\ell$ of $a$, the assignment $x=\mathrm{val}|_V$ (after complementing $\ell$ if $\ell(1)=1$) is a solution of $(V,G)$; (ii) from any split of $a$ (canonical orders) this solution is computed in polynomial time from the instance code and the split; and (iii) Pure-Circuit reduces, by a polynomial-time search reduction, to Necklace-Splitting restricted to necklaces in which every colour occurs $2b_{\rm NOR}$, $2b_{\rm NP}$ or $2b_{\rm NOT}$ times.
--
--   Differences from the source:
--   - reading: standing assumptions of §4.2: half-sizes b_NOR ≥ 5, b_NP ≥ 4, b_NOT ≥ 3 fixed, (V, G) a Pure-Circuit instance → hypotheses 5 ≤ H.bNOR, 4 ≤ H.bNP, 3 ≤ H.bNOT and I.WellFormed; reason: the section fixes them once at its top; Definition 3.2 requires distinct gate nodes and one gate per output
--   - encoding: colour order d_1, …, d_n "arbitrarily" and the beads of Σ^c_i "in any order" → an arbitrary Layout (a permutation of the colours and, for every c and i, any permutation of the canonical Σ^c_i); reason: every choice of the page is a Layout and conversely
--   - encoding: ℓ any split, complemented if necessary so that ℓ(1) = 0; val(x) = R_{h(x)}(σ(x)) → Layout.normLab complements ℓ when lab ℓ 0 = true; Layout.val reads R with that labelling; reason: the page’s normalisation, made explicit
--   - generalization: "a polynomial-time reduction from Pure-Circuit to Necklace-Splitting" → CardinalMatching.SearchReduces PureCircuit (NSCounts {2 b_NOR, 2 b_NP, 2 b_NOT}); reason: the constructed necklaces have exactly these colour counts (§4.2), and a reduction onto this restriction is in particular one to Necklace-Splitting: its valid instances are valid and its answers are exactly the splits; it is also what Theorem 1.1 needs
--   - reading: "the construction is a polynomial-time reduction … from any split of a one computes in polynomial time a solution" → clauses (i) every split decodes to a solution for every choice of orders, (ii) a polynomial-time g outputs assignCode of that solution for the canonical necklace, (iii) the search reduction; reason: the page’s two claims about the construction, plus the reduction statement
--   - encoding: polynomial time; the pair (instance, split) → CookPvsNP.PolyTimeComputable on binary codes; the pair as I.code.map (some ∘ inl) ++ none :: (List.ofFn ℓ).map (some ∘ inr); reason: the published reduction format
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Necklace Splitting with Ten Beads per Colour is PPAD-Hard (STOC 2027 submission, sha256 d5b5449c…41ac), Theorem 4.8, p. 8 (PDF 10)

import Mathlib
import Definitions.Def_NecklacePPAD_Main_Construction
import Definitions.Def_NecklacePPAD_Main_NSCounts
import Definitions.Def_CardinalMatching_SearchReduces

set_option autoImplicit false

namespace NecklacePPAD.Main

open LpBallVI.Affine

/-- **Theorem 4.8** (Zeng, Wang, Cao, Dai, Wang, STOC 2027 submission, sha256 d5b5449c…, p. 8
(PDF 10)). For all half-sizes `b_NOR ≥ 5`, `b_NP ≥ 4`, `b_NOT ≥ 3`, the construction is a
polynomial-time reduction from Pure-Circuit to Necklace-Splitting (onto necklaces whose colours
occur `2b_NOR`, `2b_NP` or `2b_NOT` times): for every choice of orders, every split of `a` decodes
(`x = val|_V`) to a solution of `(V, G)`; from any split of the canonical `a` this solution is
computed in polynomial time; and Pure-Circuit reduces to that Necklace-Splitting problem. -/
theorem theorem_4_8 (H : HalfSizes) (hNOR : 5 ≤ H.bNOR) (hNP : 4 ≤ H.bNP) (hNOT : 3 ≤ H.bNOT) :
    (∀ I : PCInst, I.WellFormed → ∀ (L : Layout I H) (ℓ : Fin L.necklace.N → Bool),
      L.necklace.IsSplit ℓ → I.IsSolution (L.decode ℓ)) ∧
    (∃ g : List (Option (Bool ⊕ Bool)) → List Bool, CookPvsNP.PolyTimeComputable g ∧
      ∀ I : PCInst, I.WellFormed → ∀ ℓ : Fin (canonLayout I H).necklace.N → Bool,
        (canonLayout I H).necklace.IsSplit ℓ →
        g (I.code.map (some ∘ Sum.inl) ++ none :: (List.ofFn ℓ).map (some ∘ Sum.inr)) =
          assignCode ((canonLayout I H).decode ℓ)) ∧
    CardinalMatching.SearchReduces PureCircuit
      (NSCounts {2 * H.bNOR, 2 * H.bNP, 2 * H.bNOT}) := by sorry

end NecklacePPAD.Main
