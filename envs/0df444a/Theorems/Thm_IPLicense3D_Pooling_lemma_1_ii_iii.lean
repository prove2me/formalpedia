-- Prove2me | Theorems.Thm_IPLicense3D_Pooling_lemma_1_ii_iii
-- name    : IPLicense3D.Pooling.lemma_1_ii_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:25:32.247778+00:00
-- url     : https://prove2.me/theorems/85d14903-77fc-45b1-9c03-1e3d992d9c76
-- title:
--   Lemma 1(ii)–(iii), p. 2691 — the surplus is linear in f and strictly decreasing and strictly convex in r and p, depending on r + p
-- statement:
--   Consider buyer $i$ in the model of §3, with surplus $S_i(f,r) = C_{T,i} - C_{A,i}(f,r)$ under the IP license $(f,r)$, and assume the standing assumptions ($h, w, p, k_A, \ell_A, \lambda_i > 0$, $k_A < k_T$, $\ell_A < \ell_T$, $z \ge 0$). Then:
--
--   1. the surplus is linearly decreasing in the fixed fee, with slope $-1$:
--   $$
--   S_i(f,r) = S_i(0,r) - f \quad\text{for all } f, r;
--   $$
--   2. for every $f$, the map $r \mapsto S_i(f,r)$ is strictly decreasing and strictly convex on $r \ge 0$;
--   3. for every $f$ and every $r \ge 0$, the surplus, viewed as a function of the printing price $p$, is strictly decreasing and strictly convex on $p > 0$;
--   4. (equal sensitivity) the royalty and the printing price enter only through $r + p$: raising $r$ by $\delta$ has the same effect as raising $p$ by $\delta$.
--
--   These properties drive the existence of the maximum royalty and fixed fees (Corollary 1) and the single-crossing argument behind Lemma 2.
--
--   **Formalization Note** Part 3 and part 4 use the surplus with the printing price as an explicit argument (`surplusF`). The domains $r \ge 0$ and $p > 0$ keep $r + p > 0$, where every square root has a positive radicand.
-- source:
--   Zhang, Westerweel, Basten & Song, Distributed 3D Printing of Spare Parts via IP Licensing, MSOM 24(5) 2022, p. 2691, Lemma 1(ii)–(iii); proof p. 2699

import Mathlib
import Definitions.Def_IPLicense3D_Pooling_Model

namespace IPLicense3D.Pooling
open Model

theorem lemma_1_ii_iii {n : ℕ} (M : Model n) (hM : M.Standing) (i : Fin n) :
    (∀ f r : ℝ, M.surplus i f r = M.surplus i 0 r - f) ∧
    (∀ f : ℝ, StrictAntiOn (fun r => M.surplus i f r) (Set.Ici 0) ∧
      StrictConvexOn ℝ (Set.Ici 0) (fun r => M.surplus i f r)) ∧
    (∀ f r : ℝ, 0 ≤ r →
      StrictAntiOn (fun p' => surplusF M.h M.w p' M.kT M.kA M.ellT M.ellA M.z (M.lam i) f r) (Set.Ioi 0) ∧
      StrictConvexOn ℝ (Set.Ioi 0)
        (fun p' => surplusF M.h M.w p' M.kT M.kA M.ellT M.ellA M.z (M.lam i) f r)) ∧
    (∀ f r δ : ℝ, surplusF M.h M.w M.p M.kT M.kA M.ellT M.ellA M.z (M.lam i) f (r + δ) =
      surplusF M.h M.w (M.p + δ) M.kT M.kA M.ellT M.ellA M.z (M.lam i) f r) := by sorry

end IPLicense3D.Pooling
