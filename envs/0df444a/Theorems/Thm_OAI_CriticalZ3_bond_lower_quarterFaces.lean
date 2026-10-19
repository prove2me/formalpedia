-- Prove2me | Theorems.Thm_OAI_CriticalZ3_bond_lower_quarterFaces
-- name    : OAI.CriticalZ3.bond_lower_quarterFaces
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:52:42.068889+00:00
-- url     : https://prove2.me/theorems/02c34979-d1c5-4757-9731-1f58f2b29790
-- title:
--   Quarter-face crossings in bond percolation below a supercritical parameter
-- statement:
--   For a centre $c\in\mathbb Z^3$ and $n\in\mathbb N$, the cube $\Lambda_n(c)$ has boundary the points with some coordinate $c_i\pm n$; it is the union of $24$ quarter-faces, each lying in one face plane $x_k=c_k\pm n$ with the other coordinates in a fixed half-range $[c_i,c_i+n]$ or $[c_i-n,c_i]$. Let $p>0$, $\gamma>0$ and $m\in\mathbb N$, and suppose that for bond percolation
--   $$
--   \mathbb P_p\bigl(\text{no vertex of }\Lambda_m(0)\text{ has an infinite cluster}\bigr)<(\gamma/2)^{24}.
--   $$
--   Then for any finite set of radii $n\ge m$ there is $q\in(p/2,p)$ such that for all those $n$, all centres $c$ and all quarter-faces $f$, with probability greater than $1-\gamma$ under $\mathbb P_q$, some vertex of $\Lambda_m(c)$ is joined to the quarter-face $f$ by open bonds inside $\Lambda_n(c)$.
--
--   This is the square-root trick turning a positive infinite-cluster probability into crossings of every quarter-face.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/QuarterFaces.lean#L364-L381

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces

open OAI OAI.CriticalZ3
universe uE uI uV uW
open MeasureTheory ProbabilityTheory Classical
open Filter Topology Classical

theorem OAI.CriticalZ3.bond_lower_quarterFaces {p γ : ℝ} (hp : 0 < p) (hγ : 0 < γ)
    {m : ℕ} (hseed : (bondLaw p).real (bondSeedInfinite 0 m)ᶜ < (γ/2)^24)
    (s : Finset ℕ) (hs : ∀ n ∈ s, m ≤ n) :
    ∃ q ∈ Set.Ioo (p/2) p, ∀ n ∈ s, ∀ c f,
      1-γ < (bondLaw q).real (bondSeedReaches c m n (QuarterFace c n f)) := by sorry
