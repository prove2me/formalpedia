-- Prove2me | Theorems.Thm_IPLicense3D_Pooling_corollary_2
-- name    : IPLicense3D.Pooling.corollary_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:25:29.30188+00:00
-- url     : https://prove2.me/theorems/8b3c2627-611e-40de-b6d1-b1c2564b93bc
-- title:
--   Corollary 2, p. 2692 — licensing profit plus buyer surplus never exceeds the maximum surplus
-- statement:
--   Under the standing assumptions of §3, for every buyer $i$ and every valid IP license $(f,r)$ with $f, r \ge 0$,
--   $$
--   \Pi_{A,i}(f,r) + S_i(f,r) \le \bar S_i ,
--   $$
--   where $\Pi_{A,i}(f,r) = f + r\lambda_i$ is the OEM's licensing profit from buyer $i$ and $\bar S_i = S_i(0,0)$ is the buyer's maximum surplus.
--
--   The OEM's profit from a licensee plus that licensee's remaining surplus is bounded by the surplus under free licensing. This bound motivates the efficacy measure (11) and is the dominance bound behind Propositions 2 and 3.
--
--   **Formalization Note** The restriction $r \ge 0$ (part of the definition of a valid license) and the standing assumption $z \ge 0$ are needed: the proof uses $r\,h\,(\lambda_i\ell_A + z\sqrt{\lambda_i\ell_A}) \ge 0$.
-- source:
--   Zhang, Westerweel, Basten & Song, Distributed 3D Printing of Spare Parts via IP Licensing, MSOM 24(5) 2022, p. 2692, Corollary 2; proof p. 2699

import Mathlib
import Definitions.Def_IPLicense3D_Pooling_Model

namespace IPLicense3D.Pooling
open Model

theorem corollary_2 {n : ℕ} (M : Model n) (hM : M.Standing) (i : Fin n) (f r : ℝ)
    (hf : 0 ≤ f) (hr : 0 ≤ r) :
    M.profitA i f r + M.surplus i f r ≤ M.maxSurplus i := by sorry

end IPLicense3D.Pooling
