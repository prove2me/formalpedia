-- Prove2me | Theorems.Thm_OffGridStorage_TechChoice_lemma_1_ii
-- name    : OffGridStorage.TechChoice.lemma_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:53.37942+00:00
-- url     : https://prove2.me/theorems/2410cb96-9486-4e0f-b63f-ce5ba22f98ff
-- title:
--   Lemma 1, second bullet, p. 12 — g0 depends on (c_K, e) only through c_K/e and is strictly increasing in it
-- statement:
--   Write $g_0(c_Q,r)=c_Q+r+\sqrt{c_Q^2+2c_Qr}$. Then
--
--   1. for every parameter set, $g_0=g_0(c_Q,c_K/e)$, i.e. the threshold depends on the storage technology only through its cost-to-efficiency ratio $c_K/e$;
--   2. for every $c_Q>0$, the map $r\mapsto g_0(c_Q,r)$ is strictly increasing on $[0,\infty)$.
--
--   The threshold does not involve $D_H$ or $D_L$, so the monotonicity holds for any demands. Together with Lemma 1's first bullet this means a lower cost-to-efficiency ratio makes storage profitable for a wider range of backup costs.
-- source:
--   Kaps, Marinesi & Netessine, When Should the Off-grid Sun Shine at Night?, SSRN 3761397 (version of May 11, 2023), p. 12, Lemma 1, second bullet, and the paragraph following it

import Mathlib
import Definitions.Def_OffGridStorage_TechChoice_Model

namespace OffGridStorage.TechChoice

/-- Lemma 1, second bullet, p. 12: `g0` depends on `(c_K, e)` only through `c_K/e`, and is
strictly increasing in that ratio for every `c_Q > 0` (it does not involve `D_H`, `D_L`). -/
theorem lemma_1_ii :
    (∀ p : Params, g0 p = g0ratio p.cQ (p.cK / p.e)) ∧
    (∀ cQ : ℝ, 0 < cQ → StrictMonoOn (g0ratio cQ) (Set.Ici 0)) := by sorry

end OffGridStorage.TechChoice
