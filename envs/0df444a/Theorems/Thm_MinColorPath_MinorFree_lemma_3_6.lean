-- Prove2me | Theorems.Thm_MinColorPath_MinorFree_lemma_3_6
-- name    : MinColorPath.MinorFree.lemma_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:11:12.324969+00:00
-- url     : https://prove2.me/theorems/1407e9aa-261d-408c-ac6c-eb03c514509e
-- title:
--   Lemma 3.6 — reduction to a semi-clean minor, computable and liftable in polynomial time
-- statement:
--   Let $\mathcal G=(G,P,\mathrm{cl})$ be a colored graph with $s,t\in V(G)$ and $r=|\mathrm{cl}(s)\cup\mathrm{cl}(t)|$. There is a semi-clean colored graph $\mathcal G'=(G',P',\mathrm{cl}')$ with $s,t\in V(G')$ such that (i) $\mathrm{ply}(\mathcal G')\le\mathrm{ply}(\mathcal G)$, $\mathrm{cs}(\mathcal G')\le\mathrm{cs}(\mathcal G)$, $\mathrm{cdeg}(\mathcal G')\le\mathrm{cdeg}(\mathcal G)$; (ii)
--   $$\mathrm{cdist}(\mathcal G',s,t)\le\mathrm{cdist}(\mathcal G,s,t)-r;$$
--   (iii) from an $(s,t)$-path $\pi'$ of $\mathcal G'$ one finds in polynomial time an $(s,t)$-path $\pi$ of $\mathcal G$ with $|\mathrm{cl}(V(\pi))|\le|\mathrm{cl}'(V(\pi'))|+r$; (iv) $G'$ is a minor of $G$; and $\mathcal G'$ is computable in polynomial time. Both algorithmic clauses are stated with fixed word-RAM programs running in $N^C$ steps on words of $W\ge b(\lfloor\log_2N\rfloor+1)$ bits, $N=\max(n,|P|,2)$. This is the first step of the proof of Theorem 1.1: it keeps the base graph $K_{3,h}$-minor-free.
--
--   Differences from the source:
--   - reading: 'G′ can be computed in polynomial time' and (iii) 'one can find in polynomial time' → two word-RAM programs prog and lift and constants b, C fixed before the instance; on every input code and word width W ≥ b(⌊log₂ N⌋ + 1) each accepts within N^C steps, N = max(n, p, 2); prog writes an input code of (G′, cl′, s′, t′) into the cells after its input; lift reads the code of G, then the code of G′, then ℓ and the vertices of π′, and writes ℓ and the vertices of π; reason: the paper names no machine; polynomial time on the published word RAM with logarithmic words, outputs read from memory; polynomial in max(n, p) is polynomial in the input size (the code has at least max(n, p) and at most polynomially many words in n, p), whereas N = max(n, 2) alone is not (one vertex may carry all p colors, and then G′ cannot even be written in n^C steps on log n-bit words)
--   - reading: G′ = (G′, P′, cl′) with s, t ∈ V(G′), and (iv) G′ is a minor of G → G′ on Fin n′ with palette Fin p′ and designated terminals s′, t′, and an explicit branch-set minor model β : Fin n′ → Set (Fin n) (nonempty, connected, pairwise disjoint branch sets, an edge of G between the branch sets of every edge of G′) with s ∈ β s′ and t ∈ β t′; reason: the model is the body of the published IsMinor plus the two memberships that say the vertices s, t of G survive as s′, t′; s′ = t′ is possible when s, t lie in one uncolored component, as in the proof
--   - encoding: (ii) cdist(G′, s, t) ≤ cdist(G, s, t) − r → cdist G′ cl′ s′ t′ + r ≤ cdist G cl s t in ℕ∞; reason: every (s, t)-path contains s and t, so cdist(G, s, t) ≥ r; both forms agree, also when there is no path (⊤)
--   - encoding: a colored graph G with |V(G)| = n and palette P; G′ with palette P′ → G : SimpleGraph (Fin n), cl : Fin n → Finset (Fin p) with palette Finset.univ; G′ likewise on Fin n′, Fin p′; reason: finite sets relabelled; every instance is isomorphic to one of this form
--   - encoding: cdist(G, s, t), the minimum colored length of an (s, t)-path → cdist G cl s t : ℕ∞, ⊤ when there is no path; G − Q is the coloring fun v => cl v \ Q; reason: the minimum over the empty set is +∞; G − Q changes only the coloring
-- source:
--   Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, Algorithms for Min-Color Path with Bounded Color-Degree, STOC 2027 submission (manuscript sha256 a088a67b…), p. 20, Lemma 3.6

import Mathlib
import Definitions.Def_MinColorPath_MinorFree_Machine
import Definitions.Def_MinColorPath_MinorFree_ColoredGraph

set_option autoImplicit false

namespace MinColorPath.MinorFree

/-- **Lemma 3.6** (p. 20). Reduction to a semi-clean minor: a fixed word-RAM program computes,
from every input code of `(G, cl, s, t)`, the code of a semi-clean colored graph `G'` with
terminals `s', t'` such that (i) ply, cs and cdeg do not increase, (ii)
`cdist(G', s', t') + r ≤ cdist(G, s, t)` with `r = |cl(s) ∪ cl(t)|`, (iv) `G'` is a minor of `G`
whose branch sets of `s', t'` contain `s, t`; and (iii) a second fixed program lifts every
`(s', t')`-path `π'` of `G'` to an `(s, t)`-path `π` of `G` with `|cl(V(π))| ≤ |cl'(V(π'))| + r`.
Both run in time `N^C` on words of `W ≥ b (⌊log₂ N⌋ + 1)` bits, `N = max(n, p, 2)`. -/
theorem lemma_3_6 :
    ∃ (prog lift : List TrulySubcubicAPSP.Instr) (b C : ℕ),
      ∀ (n p : ℕ) (G : SimpleGraph (Fin n)) (cl : Fin n → Finset (Fin p)),
        IsColoredGraph G Finset.univ cl →
        ∀ (s t : Fin n) (I : InputCode G cl) (W : ℕ), WideEnough b (max (max n p) 2) W →
        ∃ m, TrulySubcubicAPSP.exec prog ((max (max n p) 2) ^ C) 0
            (TrulySubcubicAPSP.loadWords W (I.words s t)) = some (true, m) ∧
          ∃ (n' p' : ℕ) (G' : SimpleGraph (Fin n')) (cl' : Fin n' → Finset (Fin p'))
            (s' t' : Fin n') (I' : InputCode G' cl'),
            CellsHold m (I.words s t).length (I'.words s' t') ∧
            IsColoredGraph G' Finset.univ cl' ∧ IsSemiClean G' cl' s' t' ∧
            -- (i)
            ply cl' ≤ ply cl ∧ cs Finset.univ cl' ≤ cs Finset.univ cl ∧
            cdeg Finset.univ cl' ≤ cdeg Finset.univ cl ∧
            -- (ii)
            cdist G' cl' s' t' + ((cl s ∪ cl t).card : ℕ∞) ≤ cdist G cl s t ∧
            -- (iv) a branch-set minor model of `G'` in `G` with `s ∈ β s'`, `t ∈ β t'`
            (∃ β : Fin n' → Set (Fin n),
              (∀ a, (β a).Nonempty ∧ (G.induce (β a)).Connected) ∧
              Pairwise (fun a a' => Disjoint (β a) (β a')) ∧
              (∀ a a', G'.Adj a a' → ∃ x ∈ β a, ∃ y ∈ β a', G.Adj x y) ∧
              s ∈ β s' ∧ t ∈ β t') ∧
            -- (iii)
            ∀ π' : G'.Walk s' t', π'.IsPath →
              ∃ m', TrulySubcubicAPSP.exec lift ((max (max n p) 2) ^ C) 0
                  (TrulySubcubicAPSP.loadWords W (I.words s t ++ I'.words s' t' ++
                    ((π'.support.length : Int) :: π'.support.map fun v => (v.val : Int)))) =
                  some (true, m') ∧
                ∃ π : G.Walk s t, π.IsPath ∧
                  OutputsList m' (I.words s t ++ I'.words s' t' ++
                    ((π'.support.length : Int) :: π'.support.map fun v => (v.val : Int))).length
                    π.support ∧
                  colLen cl π ≤ colLen cl' π' + (cl s ∪ cl t).card := by sorry

end MinColorPath.MinorFree
