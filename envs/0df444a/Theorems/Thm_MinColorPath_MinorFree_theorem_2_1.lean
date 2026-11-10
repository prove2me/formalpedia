-- Prove2me | Theorems.Thm_MinColorPath_MinorFree_theorem_2_1
-- name    : MinColorPath.MinorFree.theorem_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:14:08.655196+00:00
-- url     : https://prove2.me/theorems/283b75a6-248b-4dd5-bd83-54ba69877d70
-- title:
--   Theorem 2.1 — Combine&Filter is no worse than any (w, c)-good path, in time (cdeg+1)^{O(w)} n^{O(w+c)}
-- statement:
--   Let $k\in\mathbb N_0$ and suppose (*) there is an $(s,t)$-path $\pi$ of the colored graph $\mathcal G$ with $|\mathrm{cl}(V(\pi))|=k$ whose $0$-diagram has a binary tree decomposition of chromatic width at most $w$ in which the crossing number of $\pi$ is at most $c$ and $s,t\in\beta(x)$ for all $x$. Then the path $\pi^*$ returned by Algorithm 1 on $(\mathcal G,s,t,w,c)$ is an $(s,t)$-path with
--   $$|\mathrm{cl}(V(\pi^*))|\le k,$$
--   and Algorithm 1 runs in time $(\mathrm{cdeg}(\mathcal G)+1)^{O(w)}n^{O(w+c)}$. In Lean: (a) every run returns a path and every path a run can return has colored length at most $k$; (b) one fixed word-RAM program computes a run of Algorithm 1 within $(\mathrm{cdeg}+1)^{Cw+C}\,N^{C(w+c)+C}$ steps, $N=\max(n,2)$, on every input and every word width $W\ge b(\lfloor\log_2\max(n,|P|,w,c,2)\rfloor+1)$. Theorem 1.1 is this theorem combined with Theorem 7.1.
--
--   Differences from the source:
--   - reading: 'the path π∗ returned by Algorithm 1' → (a) for every run Fs: some path is an output of Fs (IsOutput), and every output of Fs has colored length ≤ k; reason: each arg min is an arbitrary choice; the claim holds for every choice
--   - reading: time complexity (cdeg(G)+1)^{O(w)} n^{O(w+c)} → one program prog and constants b, C fixed before (G, s, t, w, c); on input code ++ [w, c] it accepts within (cdeg + 1)^{C·w + C} · N^{C·(w+c) + C} steps, N = max(n, 2); reason: O(x) read as at most Cx + C: the literal C·w, C·(w + c) is false at w = c = 0, where the n + |P| rounds and the output still cost time
--   - reading: Algorithm 1 as an algorithm → the program's output cells hold an output path of some run Fs of the Algorithm 1 model, or −1 when that run has no output (empty F∗; line 7 of Algorithm 1 is undefined there); reason: the paper's time claim is for the algorithm on every input; the no-output case is not specified on the page
--   - reading: word RAM with O(log n)-bit words → W ≥ b(⌊log₂ max(n, p, w, c, 2)⌋ + 1); reason: the parameters w and c and the colors (up to p, which no polynomial in n bounds) are input words and must fit in a word; with words of only O(log n) bits an instance whose palette is far larger than n (one vertex may carry all p colors) has an input longer than the addressable memory, and no program can even write its output there; log max(n, p) is the log of the input size up to a constant factor
--   - encoding: part (b) on an arbitrary colored graph → Fin n, palette Fin p (Finset.univ), input code InputCode; reason: every instance is isomorphic to one of this form; part (a) is stated on arbitrary types
--   - encoding: a finite simple graph G with palette P and coloring cl : V(G) → 2^P → a SimpleGraph V on a finite type V, colors in a type C, palette P : Finset C, cl : V → Finset C, with IsColoredGraph G P cl (cl v ⊆ P; V_τ nonempty and G[V_τ] preconnected for τ ∈ P); reason: the definition of p. 17 written on types; the same instances
--   - encoding: a rooted (binary) tree decomposition (T, β) → RTD: the published IsTreeDecomposition on a finite node type plus a root; T_x, γ(x), children and height defined from the root paths; binary = at most two children; reason: the path condition (iii) of the published definition is equivalent to the connected-subtree condition; finite trees as in the paper
--   - encoding: the d-diagram D with vertex set V(G′) ∪ P′, cl′(v) = cl(v), cl′(τ) = {τ}; s, t ∈ β(x) → diagGraph cl d H on the sum type ↥V(G′) ⊕ ↥P′ (G′ = π.toSubgraph for a path), coloring diagCl; s ∈ β(x) is baseIn (the base copy of s lies in the bag); reason: the vertex set is a disjoint union of the base part and the color part
--   - encoding: an (s, t)-path π and its x-segments, the connected components of π[γ(x)] → π : G.Walk s t with π.IsPath; x-segments are the maximal runs [i, j] of consecutive positions of π.support (0-based, from the s-side) inside γ(x); reason: the edges of a path are its consecutive pairs, so the components of π[γ(x)] are exactly these runs
--   - encoding: cdist(G, s, t), the minimum colored length of an (s, t)-path → cdist G cl s t : ℕ∞, ⊤ when there is no path; G − Q is the coloring fun v => cl v \ Q; reason: the minimum over the empty set is +∞; G − Q changes only the coloring
-- source:
--   Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, Algorithms for Min-Color Path with Bounded Color-Degree, STOC 2027 submission (manuscript sha256 a088a67b…), p. 21, Theorem 2.1

import Mathlib
import Definitions.Def_MinColorPath_MinorFree_CombineFilter
import Definitions.Def_MinColorPath_MinorFree_Machine

set_option autoImplicit false

namespace MinColorPath.MinorFree

/-- **Theorem 2.1** (p. 21). (a) If some `(s, t)`-path `π` with `|cl(V(π))| = k` has a binary tree
decomposition of its 0-diagram of chromatic width at most `w`, crossing number of `π` at most `c`
and `s, t` in every bag, then every run of Algorithm 1 on `(G, s, t, w, c)` returns an
`(s, t)`-path, and every path it can return has colored length at most `k`. (b) One fixed
word-RAM program computes a run of Algorithm 1 (reporting `−1` when that run has nothing to
return) in time `(cdeg(G)+1)^{Cw+C} · N^{C(w+c)+C}`, `N = max(n, 2)`, on every input
and every word width `W ≥ b (⌊log₂ max(n, p, w, c, 2)⌋ + 1)`. -/
theorem theorem_2_1 :
    (∀ {V C : Type} [Fintype V] [DecidableEq V] [DecidableEq C]
      (G : SimpleGraph V) (P : Finset C) (cl : V → Finset C), IsColoredGraph G P cl →
      ∀ (s t : V) (w c k : ℕ),
        (∃ π : G.Walk s t, π.IsPath ∧ colLen cl π = k ∧
          ∃ 𝒯 : RTD (pathDiag cl 0 π), 𝒯.IsBinary ∧ IsGood 𝒯 w c) →
        ∀ Fs : ℕ → Finset (Finset C), IsRun G P cl w c Fs →
          (∃ π' : G.Walk s t, IsOutput G P cl s t Fs π') ∧
          ∀ π' : G.Walk s t, IsOutput G P cl s t Fs π' → colLen cl π' ≤ k) ∧
    ∃ (prog : List TrulySubcubicAPSP.Instr) (b C : ℕ),
      ∀ (n p : ℕ) (G : SimpleGraph (Fin n)) (cl : Fin n → Finset (Fin p)),
        IsColoredGraph G Finset.univ cl →
        ∀ (s t : Fin n) (I : InputCode G cl) (w c W : ℕ),
          WideEnough b (max (max (max n p) 2) (max w c)) W →
          ∃ m, TrulySubcubicAPSP.exec prog
              ((cdeg Finset.univ cl + 1) ^ (C * w + C) * (max n 2) ^ (C * (w + c) + C)) 0
              (TrulySubcubicAPSP.loadWords W (I.words s t ++ [(w : Int), (c : Int)])) =
              some (true, m) ∧
            ∃ Fs : ℕ → Finset (Finset (Fin p)), IsRun G Finset.univ cl w c Fs ∧
              ((∃ π' : G.Walk s t, IsOutput G Finset.univ cl s t Fs π' ∧
                  OutputsList m ((I.words s t).length + 2) π'.support) ∨
                ((¬ ∃ π' : G.Walk s t, IsOutput G Finset.univ cl s t Fs π') ∧
                  OutputsNoPath m ((I.words s t).length + 2))) := by sorry

end MinColorPath.MinorFree
