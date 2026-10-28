-- Prove2me | Theorems.Thm_IPLicense3D_Pooling_lemma_1_vi
-- name    : IPLicense3D.Pooling.lemma_1_vi
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:25:31.507332+00:00
-- url     : https://prove2.me/theorems/25c3ea44-c05a-45d3-83ef-e0c637617d8b
-- title:
--   Lemma 1(vi), p. 2691 — the surplus is increasing and concave in the wholesale price w
-- statement:
--   Under the standing assumptions of §3, fix buyer $i$ and the license $(f, r)$, and view the surplus $S_i(f,r)$ as a function of the wholesale price $w$, all other parameters held fixed. On $w > 0$ this function is increasing and concave:
--   $$
--   w \mapsto S_i(f,r) \ \text{ is nondecreasing and concave on } (0,\infty).
--   $$
--
--   Only the traditional cost $C_{T,i}$ depends on $w$. This lemma is the source of the "Moreover" clauses of Propositions 2 and 3: the OEM's optimal profit increases in $w$.
--
--   **Formalization Note** The statement uses the surplus with $w$ as an explicit argument (`surplusF`). "Increasing" is stated in the weak sense (`MonotoneOn`), as printed.
-- source:
--   Zhang, Westerweel, Basten & Song, Distributed 3D Printing of Spare Parts via IP Licensing, MSOM 24(5) 2022, p. 2691, Lemma 1(vi); proof p. 2699

import Mathlib
import Definitions.Def_IPLicense3D_Pooling_Model

namespace IPLicense3D.Pooling
open Model

theorem lemma_1_vi {n : ℕ} (M : Model n) (hM : M.Standing) (i : Fin n) (f r : ℝ) :
    MonotoneOn (fun w' => surplusF M.h w' M.p M.kT M.kA M.ellT M.ellA M.z (M.lam i) f r) (Set.Ioi 0) ∧
    ConcaveOn ℝ (Set.Ioi 0)
      (fun w' => surplusF M.h w' M.p M.kT M.kA M.ellT M.ellA M.z (M.lam i) f r) := by sorry

end IPLicense3D.Pooling
