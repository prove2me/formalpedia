-- Prove2me | Theorems.Thm_OPG37364_lps13_remaining_core
-- name    : OPG37364.lps13_remaining_core
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T16:12:57.61053+00:00
-- url     : https://prove2.me/theorems/82643fa0-e4f4-4842-a49f-d2b748cdbca1
-- title:
--   Remaining connectedness, girth and weak spectrum for the concrete LPS13 graphs
-- statement:
--   For every integer $g\ge3$ there is a threshold $B$ such that the following holds. Let $q>\max\{B,13\}$ be prime, assume $13$ is a quadratic nonresidue modulo $q$, and choose any $i\in\mathbb F_q$ with $i^2=-1$. Then the already-defined fixed-$p=13$ graph $X_{13,q,i}$ on $\operatorname{PGL}_2(\mathbb F_q)$ is connected, has girth at least $g$, and its real adjacency matrix satisfies
--
--   $$\mu\in\operatorname{spec}_{\mathbb R}(A_{13,q,i}),\quad \mu\ne14\quad\Longrightarrow\quad\mu<12.$$
--
--   Here $X_{13,q,i}$ is precisely the graph in Definitions.Def_opg37364_lps13, using the fourteen norm-$13$ quaternion generators and right Cayley multiplication. The threshold is common to the three properties and is allowed to depend on $g$. No numerical value for it is specified. The choice of a finite enumeration in the formal statement serves only to form the adjacency matrix.
--
--   This is the explicitly unresolved LPS core. Construction, $14$-regularity, bipartiteness under the nonresidue hypothesis, and arbitrarily large suitable primes have separate completed proofs and are not included among its conclusions. The bound is a weaker sufficient consequence of the published LPS/DSV spectral estimates, not a claim that the full Ramanujan theorem has been formalized. No immunity, matching, cut-expansion or Markov-gap assertion is part of this statement.
-- source:
--   Davidoff–Sarnak–Valette, Elementary Number Theory, Group Theory, and Ramanujan Graphs (2003), Proposition 2.5.2 and Section 4.2 for the chosen quaternion-to-PGL Cayley model; Proposition 4.3.3, Theorem 4.3.5 and Corollary 4.3.6 for girth and sufficiently-large-q connectedness; Theorem 4.4.4 for the eventual weak nontrivial spectral bound. https://math.bme.hu/~gabor/oktatas/SztoM/DavidoffSarnakValette.pdf . Specialize p=13 and epsilon=1/24: 13^(7/8)+13^(1/8)<12; the exceptional negative eigenvalue -14 also satisfies the required one-sided bound. The common threshold absorbs these three conditions. This is a source-supported remaining-core specification, not a verbatim source theorem and not a completed proof. The stronger LPS Ramanujan result also implies the spectral part: Lubotzky–Phillips–Sarnak, Ramanujan graphs, Combinatorica 8 (1988), https://doi.org/10.1007/BF02126799 .

import Definitions.Def_opg37364_lps13
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic

set_option autoImplicit false
open scoped Classical

namespace OPG37364

theorem lps13_remaining_core :
    ∀ g : ℕ, 3 ≤ g →
      ∃ B : ℕ, ∀ (q : ℕ) [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q),
        B < q → legendreSym q 13 = -1 →
        letI : Fintype (Matrix.ProjGenLinGroup (Fin 2) (ZMod q)) := Fintype.ofFinite _
        IsConnected (lps13Graph hq i) ∧ HasGirthAtLeast (lps13Graph hq i) g ∧
          (∀ μ : ℝ, μ ∈ spectrum ℝ ((lps13Graph hq i).adjMatrix ℝ) →
            μ ≠ 14 → μ < 12) := by sorry

end OPG37364
