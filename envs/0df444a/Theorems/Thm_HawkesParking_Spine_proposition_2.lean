-- Prove2me | Theorems.Thm_HawkesParking_Spine_proposition_2
-- name    : HawkesParking.Spine.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:26.581706+00:00
-- url     : https://prove2.me/theorems/6cc3157c-c941-428e-b3f8-830035e4d260
-- title:
--   Proposition 2, p. 14 — the order statistics of $d-U$ are uniform on $\bar{\mathcal P}_{k,d}$
-- statement:
--   Let $k\ge 1$, let $d\in\mathsf D_k$ be a $k$-step Dyck path, and let $U=(U_1,\dots,U_k)$ have i.i.d. $\mathrm{Uni}(0,1)$ coordinates. Let $X_d$ be the vector of order statistics of $d-U=(d_1-U_1,\dots,d_k-U_k)$. Then
--   $$X_d\sim\mathrm{Uni}\big(\bar{\mathcal P}_{k,d}\big).$$
--
--   This gives a direct sampler for each region of the Dyck decomposition of Proposition 1.
--
--   **Formalization Note.** The law of $U$ is Lebesgue measure restricted to the open cube $(0,1)^k$; the statement is the equality of its image under $u\mapsto\mathrm{sort}(d-u)$ with the normalized Lebesgue measure on $\bar{\mathcal P}_{k,d}$.
-- source:
--   Daw, Conditional Uniformity and Hawkes Processes, arXiv:2202.05335v2, p. 14, Proposition 2

import Mathlib
import Definitions.Def_HawkesParking_Spine_Model

namespace HawkesParking.Spine
open MeasureTheory
theorem proposition_2 (k : ℕ) (hk : 1 ≤ k) (d : Fin k → ℕ) (hd : d ∈ dyckPaths k) :
    (volume.restrict (unitCube k)).map (fun u => sortVec fun i => (d i : ℝ) - u i) =
      unif (dyckRegion k d) := by sorry
end HawkesParking.Spine
