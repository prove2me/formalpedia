-- Prove2me | Theorems.Thm_IPLicense3D_Pooling_corollary_1
-- name    : IPLicense3D.Pooling.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:25:43.048063+00:00
-- url     : https://prove2.me/theorems/621707b6-f283-4abe-a5ac-f63f720845e2
-- title:
--   Corollary 1, p. 2691 — the maximum royalty fee r̄ᵢ(f) and maximum fixed fee f̄ᵢ(r) = Sᵢ(0, r)
-- statement:
--   Under the standing assumptions of §3, for every buyer $i$:
--
--   1. for every fixed fee $f \ge 0$ with $S_i(f,0) \ge 0$ there is a unique royalty $\bar r_i(f) \ge 0$ with $S_i(f, \bar r_i(f)) = 0$;
--   2. for every royalty $r \ge 0$ with $S_i(0,r) \ge 0$ there is a unique fixed fee $\bar f_i(r)$ with $S_i(\bar f_i(r), r) = 0$, namely
--   $$
--   \bar f_i(r) = S_i(0,r);
--   $$
--   3. $\bar r_i(f)$ decreases in $f$: if $f \le f'$, $r, r' \ge 0$, $S_i(f,r) = 0$ and $S_i(f',r') = 0$, then $r' \le r$. Also $\bar f_i(r) = S_i(0,r)$ decreases in $r$ on $r \ge 0$.
--
--   $\bar r_i(f)$ is the largest royalty buyer $i$ accepts at fixed fee $f$, and $\bar f_i(r)$ the largest fixed fee it accepts at royalty $r$. The royalty $\bar r_1(0)$ enters the case split of Proposition 3.
--
--   **Formalization Note** "Decreases" is stated in the weak sense, as printed. Part 3 characterizes $\bar r_i$ through its defining equation rather than as a function. Fees are taken nonnegative, the paper's convention for a valid license.
-- source:
--   Zhang, Westerweel, Basten & Song, Distributed 3D Printing of Spare Parts via IP Licensing, MSOM 24(5) 2022, p. 2691, Corollary 1; proof p. 2699

import Mathlib
import Definitions.Def_IPLicense3D_Pooling_Model

namespace IPLicense3D.Pooling
open Model

theorem corollary_1 {n : ℕ} (M : Model n) (hM : M.Standing) (i : Fin n) :
    (∀ f : ℝ, 0 ≤ f → 0 ≤ M.surplus i f 0 → ∃! r : ℝ, 0 ≤ r ∧ M.surplus i f r = 0) ∧
    (∀ r : ℝ, 0 ≤ r → 0 ≤ M.surplus i 0 r →
      (∃! f : ℝ, M.surplus i f r = 0) ∧ M.surplus i (M.surplus i 0 r) r = 0) ∧
    (∀ f f' r r' : ℝ, f ≤ f' → 0 ≤ r → 0 ≤ r' → M.surplus i f r = 0 → M.surplus i f' r' = 0 → r' ≤ r) ∧
    AntitoneOn (fun r => M.surplus i 0 r) (Set.Ici 0) := by sorry

end IPLicense3D.Pooling
