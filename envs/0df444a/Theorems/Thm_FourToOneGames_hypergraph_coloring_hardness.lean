-- Prove2me | Theorems.Thm_FourToOneGames_hypergraph_coloring_hardness
-- name    : FourToOneGames.hypergraph_coloring_hardness
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T23:03:21.096685+00:00
-- url     : https://prove2.me/theorems/58dbf557-c2e1-4011-8c1f-a64f5e1125cc
-- title:
--   Theorem 3.1 — hardness of approximate colouring of 3-uniform hypergraphs
-- statement:
--   For every positive integer $c$ there is a constant $\varepsilon > 0$ such that, given a 3-uniform hypergraph $H$, it is hard to distinguish the case that $H$ is $2$-colourable from the case that every $c$-colouring of $H$ leaves at least an $\varepsilon$ fraction of its edges monochromatic. This is the starting point of the outer PCP of the source paper (Theorem 3.1, proved there in Appendix A).
--
--   Hardness is formalized as the existence of a polynomial-time gap-preserving reduction from label cover with projection constraints: for every $c > 0$ there are $\varepsilon > 0$ and $s \in (0,1)$ such that for every alphabet bound $r_0$ there is a polynomial-time computable map $\Psi \mapsto H_\Psi$ sending instances with alphabets of size at most $r_0$ and $\mathrm{val}(\Psi) = 1$ to $2$-colourable hypergraphs, and instances with $\mathrm{val}(\Psi) \le s$ to hypergraphs in which every $c$-colouring leaves an $\varepsilon$ fraction of the edges monochromatic. Combined with the NP-hardness of $\mathrm{GapPLC}_{r_0}(1,s)$ (the PCP theorem plus parallel repetition, Theorem 1.2 of the source, taken here as an external input) this gives the NP-hardness stated in the paper.
--
--   The quantitative bound $\varepsilon \ge \exp(-\exp(O(c^3)))$ of the source is not part of the formal statement, which asserts only $\varepsilon > 0$.
-- source:
--   Yumou Fei, Dor Minzer, Shuo Wang, "On the Hardness of 4-to-1 Games with Perfect Completeness", ECCC Report No. TR26-179 (2026), https://eccc.weizmann.ac.il/report/2026/179/, p. 15, Theorem 3.1 (proof in Appendix A, pp. 74-80)

import Definitions.Def_FourToOneGames_LabelCover
import Definitions.Def_FourToOneGames_Hypergraph

namespace FourToOneGames

theorem hypergraph_coloring_hardness :
    ∀ c : ℕ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∀ r₀ : ℕ,
      Nonempty (GapReduction encodeLabelCover encodeHypergraph3
        (fun P : LabelCover => LabelCover.AlphabetBound r₀ P ∧ P.val = 1)
        (fun P : LabelCover => LabelCover.AlphabetBound r₀ P ∧ P.val ≤ s)
        (fun H : Hypergraph3 => H.Colorable 2)
        (fun H : Hypergraph3 => H.AllColoringsMono c ε)) := by
  sorry

end FourToOneGames
