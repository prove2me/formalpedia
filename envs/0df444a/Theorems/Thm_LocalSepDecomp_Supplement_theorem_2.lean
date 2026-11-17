-- Prove2me | Theorems.Thm_LocalSepDecomp_Supplement_theorem_2
-- name    : LocalSepDecomp.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:46:58.159648+00:00
-- url     : https://prove2.me/theorems/f7e3f5eb-1e23-4946-ac26-c2a0503d1a3d
-- title:
--   Theorem 2 — an always-halting algorithm outputs a canonical graph-decomposition, $H^{\le k}_r(G)$ when $k<K(G,r)$
-- statement:
--   There is an algorithm that receives a finite connected graph $G$ and integers $r,k\in\mathbb N$ as input, always halts, and either outputs a canonical graph-decomposition of $G$ or correctly reports that $k\ge K(G,r)$. If $k<K(G,r)$, then its output is the graph-decomposition $H^{\le k}_r(G)$ of Theorem 1.
--
--   Precisely, there is a total computable function $f$ on codes $(n,E,r,k)$ such that for every input whose coded graph $G$ is connected:
--
--   1. every output of $f$ is a well-formed code of a graph-decomposition with parts of $G$ that is canonical, i.e. admits an action of $\mathrm{Aut}(G)$ commuting with the parts (whatever $k$ is);
--   2. if $f$ reports, then $k\ge K(G,r)$;
--   3. if $k<K(G,r)$, then $f$ outputs a code whose decoding is isomorphic, with parts, to $H^{\le k}_r(G)$.
--
--   Here $K(G,r)=\Delta_r(G)/r+1$ for $r>0$ and $K(G,0)=2$, computed from the $r$-local covering of $G$. The algorithm does not decide whether $k<K(G,r)$; it only has to be correct when it reports.
--
--   **Formalization Note** The algorithm is a Mathlib-`Computable` function `ℕ × List (ℕ × ℕ) × ℕ × ℕ → Option DecompCode`; `none` is the report. $K(G,r)$ is `Kval p r` for every $r$-local covering `p`, as in the mission's goal.
--
--   Differences from the source:
--
--   - encoding: an algorithm that receives G, r, k, always halts, and outputs a graph-decomposition or a report → a total function f : ℕ × List (ℕ × ℕ) × ℕ × ℕ → Option DecompCode with Mathlib `Computable f`; none is the report k ⩾ K(G, r); reason: 'there is an algorithm that always halts' is the existence of a total computable function, independent of the machine model; without Computable the statement would be trivially true
--   - encoding: a finite connected graph G as input → a code (n, E) of a graph graphOfCode n E on Fin n, with the hypothesis that it is connected; reason: every finite graph is isomorphic to a coded one (graphOfCode_surjective, proved in the sanity file); H^{≤k}_r and K(G, r) are defined on the given graph
--   - encoding: outputs a canonical graph-decomposition of G → outputs some c with WellFormed G c, IsGraphDecomp (decodeDecomp G c) and IsCanonicalDecomp ⊤ (decodeDecomp G c), for every input with G connected and every k; reason: a finite graph-decomposition with parts is output as a finite code; canonical means Aut(G)-canonical (p.17), as in the base goal
--   - encoding: k ⩾ K(G, r), resp. k < K(G, r) → Kval p r ≤ k, resp. k < Kval p r, for every r-local covering p : C → G with C : Type; reason: K(G, r) is computed from the r-local covering as in the base goal (Kval in ℝ≥0∞); all r-local coverings are isomorphic and one exists on a type in Type
--   - encoding: its output is the graph-decomposition H^{≤k}_r(G) → the output is some c and decodeDecomp G c is isomorphic, with parts, to Hle G r k (Nonempty DecompIso); reason: a coded decomposition has node type Fin m, H^{≤k}_r(G) has the cutouts as nodes; being the same decomposition is an isomorphism preserving incidences and parts (p.54)
-- source:
--   Jacobs, Knappe, Kurkofka, Canonical Graph Decompositions via Local Separations, preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), Theorem 2, p.7 (proof p.57)

import Mathlib
import Definitions.Def_LocalSepDecomp_Cutouts
import Definitions.Def_LocalSepDecomp_Supplement_Encoding

set_option autoImplicit false

namespace LocalSepDecomp.Supplement

open SimpleGraph

/-- **Theorem 2.** R. W. Jacobs, P. Knappe, J. Kurkofka, *Canonical Graph Decompositions via Local
Separations*, preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), Theorem 2, p.7
(proof p.57). There is an algorithm that receives a finite connected graph `G` and integers
`r, k ∈ ℕ` as input, always halts, and either outputs a canonical graph-decomposition of `G` or
correctly reports that `k ⩾ K(G, r)`. If `k < K(G, r)`, then its output is the graph-decomposition
`H^{≤k}_r(G)` of Theorem 1.

**Formalization Note.** "An algorithm that always halts" is a total function `f` that is
Mathlib-`Computable` on the codes `(n, E, r, k)`, `G = graphOfCode n E` on `Fin n`; the output
`none` is the report `k ⩾ K(G, r)`, and `some c` outputs the decomposition coded by `c`.
Without `Computable` the statement would be trivially true classically. The three clauses:
(a) for every input with `G` connected (for every `k`), an output `some c` is a well-formed code of a
graph-decomposition of `G` that is canonical (`Aut(G)`-canonical, `Γ = ⊤`); (b) the report is
correct: `K(G, r) ≤ k` computed from every `r`-local covering `p : C → G` (`Kval`, `ℝ≥0∞`);
(c) if `k < K(G, r)` the output is `some c` and the decoded decomposition is isomorphic, with
parts, to `H^{≤k}_r(G)` (`Hle`). The algorithm is not required to decide `k < K(G, r)`. -/
theorem theorem_2 :
    ∃ f : ℕ × List (ℕ × ℕ) × ℕ × ℕ → Option DecompCode, Computable f ∧
      ∀ (n : ℕ) (E : List (ℕ × ℕ)) (r k : ℕ), (graphOfCode n E).Connected →
        (∀ c, f (n, E, r, k) = some c →
            WellFormed (graphOfCode n E) c ∧ IsGraphDecomp (decodeDecomp (graphOfCode n E) c) ∧
              IsCanonicalDecomp ⊤ (decodeDecomp (graphOfCode n E) c)) ∧
          (f (n, E, r, k) = none →
            ∀ (W : Type) (C : SimpleGraph W) (p : C →g graphOfCode n E),
              IsLocalCovering (graphOfCode n E) r p → Kval p r ≤ (k : ENNReal)) ∧
          ∀ (W : Type) (C : SimpleGraph W) (p : C →g graphOfCode n E),
            IsLocalCovering (graphOfCode n E) r p → (k : ENNReal) < Kval p r →
              ∃ c, f (n, E, r, k) = some c ∧
                Nonempty (DecompIso (decodeDecomp (graphOfCode n E) c)
                  (Hle (graphOfCode n E) r k)) := by sorry

end LocalSepDecomp.Supplement
