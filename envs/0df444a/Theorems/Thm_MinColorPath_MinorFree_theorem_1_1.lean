-- Prove2me | Theorems.Thm_MinColorPath_MinorFree_theorem_1_1
-- name    : MinColorPath.MinorFree.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:11:12.568467+00:00
-- url     : https://prove2.me/theorems/7c7043fc-bd0a-4f91-b98c-56e27958197a
-- title:
--   Theorem 1.1 — exact Min-Color Path on K_{3,h}-minor-free graphs in time n^{(cdeg+1)^{O(1)}}
-- statement:
--   For every fixed integer $h\ge1$, **Min-Color Path** on $K_{3,h}$-minor-free graphs admits an algorithm with running time $n^{(\mathrm{cdeg}(\mathcal G)+1)^{O(1)}}$. Formally: there are one word-RAM program and constants $b,C$ (depending on $h$ only) such that for every colored graph $\mathcal G=(G,P,\mathrm{cl})$ on $n$ vertices whose base graph has no $K_{3,h}$ minor, all $s,t$, every input code and every word width $W\ge b(\lfloor\log_2M\rfloor+1)$, $M=\max(n,|P|,2)$, the program accepts within
--   $$N^{\,C\,(\mathrm{cdeg}(\mathcal G)+1)^{C}}$$
--   steps, $N=\max(n,2)$, and its output cells hold an $(s,t)$-path $\pi$ with $|\mathrm{cl}(V(\pi))|\le|\mathrm{cl}(V(\pi'))|$ for every $(s,t)$-path $\pi'$ when $s,t$ are connected, and $-1$ otherwise. It answers the question of Erickson–LaValle and Hauser on planar instances of bounded color-degree.
--
--   Differences from the source:
--   - reading: running time n^{(cdeg(G)+1)^{O(1)}} → exec halts and accepts within N^{C·(cdeg + 1)^C} steps, N = max(n, 2), on every input, C fixed with the program; reason: the paper's convention for X^{O(1)} (it writes (cdeg+1)^{O(1)} for 40(cdeg+1)^4); the literal exponent (cdeg+1)^C equals 1 at cdeg = 0 and is false there (insight I1); N = max(n, 2) avoids 1^x
--   - reading: an algorithm (no machine named) → one program of the published word RAM TrulySubcubicAPSP (exec, loadWords), fixed after h and before the instance, every word width W ≥ b(⌊log₂ M⌋ + 1), M = max(n, p, 2); reason: the standard word RAM with logarithmic words; h is not an input; with words of only O(log n) bits an instance whose palette is far larger than n (one vertex may carry all p colors) has an input longer than the addressable memory, and no program can even write its output there; log max(n, p) is the log of the input size up to a constant factor
--   - reading: the input of Min-Color Path (no format named) → InputCode: n, p, s, t, then the adjacency lists, then the color lists, each list duplicate-free in any order; the statement holds for every such code; reason: an explicit code; quantifying over all list orders
--   - reading: output: a path π from s to t minimizing |cl(V(π))| → the cells after the input hold ℓ and the vertices of an (s, t)-path whose colored length is ≤ that of every (s, t)-path when s, t are connected (G.Reachable), and −1 otherwise; reason: the problem does not assume s, t connected; the paper reports infeasibility in that case (p. 31)
--   - encoding: a colored graph G = (G, P, cl) with |V(G)| = n → G : SimpleGraph (Fin n), cl : Fin n → Finset (Fin p), palette Finset.univ, IsColoredGraph; reason: finite sets relabelled; every instance is isomorphic to one of this form
--   - encoding: K3,h-minor free → ¬ IsMinor (completeBipartiteGraph (Fin 3) (Fin h)) G with the published IsMinor; reason: the published branch-set definition of a minor
-- source:
--   Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, Algorithms for Min-Color Path with Bounded Color-Degree, STOC 2027 submission (manuscript sha256 a088a67b…), p. 2, Theorem 1.1 (restated p. 51, proved p. 52)

import Mathlib
import Definitions.Def_MinColorPath_MinorFree_Machine
import Definitions.Def_MinColorPath_MinorFree_ColoredGraph
import Definitions.Def_RobertsonSeymour1986_GM5_IsMinor

set_option autoImplicit false

namespace MinColorPath.MinorFree

/-- **Theorem 1.1** (p. 2). For every fixed integer `h ≥ 1` there are one word-RAM program and
constants `b, C` such that on every input code of every colored graph `(G, Fin p, cl)` on `Fin n`
whose base graph has no `K_{3,h}` minor, with terminals `s, t`, and every word width
`W ≥ b (⌊log₂ M⌋ + 1)`, `M = max(n, p, 2)`, the program accepts within `N^{C (cdeg(G)+1)^C}` steps,
`N = max(n, 2)`,
and its output cells hold an `(s, t)`-path of minimum colored length when `s` and `t` are
connected, and `−1` otherwise. -/
theorem theorem_1_1 :
    ∀ h : ℕ, 1 ≤ h → ∃ (prog : List TrulySubcubicAPSP.Instr) (b C : ℕ),
      ∀ (n p : ℕ) (G : SimpleGraph (Fin n)) (cl : Fin n → Finset (Fin p)),
        IsColoredGraph G Finset.univ cl →
        ¬ RobertsonSeymour1986.GM5.IsMinor (completeBipartiteGraph (Fin 3) (Fin h)) G →
        ∀ (s t : Fin n) (I : InputCode G cl) (W : ℕ), WideEnough b (max (max n p) 2) W →
        ∃ m, TrulySubcubicAPSP.exec prog ((max n 2) ^ (C * (cdeg Finset.univ cl + 1) ^ C)) 0
            (TrulySubcubicAPSP.loadWords W (I.words s t)) = some (true, m) ∧
          (G.Reachable s t → ∃ π : G.Walk s t, π.IsPath ∧
            OutputsList m (I.words s t).length π.support ∧
            ∀ π' : G.Walk s t, π'.IsPath → colLen cl π ≤ colLen cl π') ∧
          (¬ G.Reachable s t → OutputsNoPath m (I.words s t).length) := by sorry

end MinColorPath.MinorFree
