-- Prove2me | Theorems.Thm_OAI_CriticalZ3_site_lower_quarterFaces
-- name    : OAI.CriticalZ3.site_lower_quarterFaces
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:53:13.579023+00:00
-- url     : https://prove2.me/theorems/025aae0b-29b4-4bf2-a46e-a7c8c5aa91e6
-- title:
--   Quarter-face crossings in site percolation below a supercritical parameter
-- statement:
--   For a centre $c\in\mathbb Z^3$ and $n\in\mathbb N$, the cube $\Lambda_n(c)$ has boundary the points with some coordinate $c_i\pm n$; it is the union of $24$ quarter-faces, each lying in one face plane $x_k=c_k\pm n$ with the other coordinates in a fixed half-range $[c_i,c_i+n]$ or $[c_i-n,c_i]$. Let $p>0$, $\gamma>0$ and $m\in\mathbb N$, and suppose that for site percolation
--   $$
--   \mathbb P_p\bigl(\text{no vertex of }\Lambda_m(0)\text{ has an infinite cluster}\bigr)<(\gamma/2)^{24}.
--   $$
--   Then for any finite set of radii $n\ge m$ there is $q\in(p/2,p)$ such that for all those $n$, all centres $c$ and all quarter-faces $f$, with probability greater than $1-\gamma$ under $\mathbb P_q$, some open vertex of $\Lambda_m(c)$ is joined to the quarter-face $f$ by open sites inside $\Lambda_n(c)$.
--
--   It is the site-percolation counterpart of the bond statement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/QuarterFaces.lean#L383-L398

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

theorem OAI.CriticalZ3.site_lower_quarterFaces {p γ : ℝ} (hp : 0 < p) (hγ : 0 < γ)
    {m : ℕ} (hseed : (siteLaw p).real (siteSeedInfinite 0 m)ᶜ < (γ/2)^24)
    (s : Finset ℕ) (hs : ∀ n ∈ s, m ≤ n) :
    ∃ q ∈ Set.Ioo (p/2) p, ∀ n ∈ s, ∀ c f,
      1-γ < (siteLaw q).real (siteSeedReaches c m n (QuarterFace c n f)) := by sorry
