-- Prove2me | Theorems.Thm_LimitsLifting_Approximation_claim_4_8
-- name    : LimitsLifting.Approximation.claim_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:38:57.650339+00:00
-- url     : https://prove2.me/theorems/b15db6e7-00d1-4f17-ba66-b341f15fc9dd
-- title:
--   Claim 4.8 — $A$ is injective and $|B(\{0,1\}^{mn})|\ge(1-2n\cdot2^{-m})2^{mn}$
-- statement:
--   Let $F$ be an unsatisfiable CNF over $[n]$ in which every variable occurs and no clause contains a literal and its negation, and let $A:[m]^n\to\{0,1\}^{\mathcal R}$ and $B:\{0,1\}^{mn}\to\{0,1\}^{\mathcal R}$ be the maps of Razborov's reduction for the canonical cover $\mathcal R=\mathcal R_{F,\mathrm{Ind}_m}$, with $m\ge1$. Then $A$ is injective, and
--   $$|B(\{0,1\}^{mn})|\ge(1-2n\cdot 2^{-m})\cdot 2^{mn}.$$
--
--   The positive class consists of distinct images under the injective map $A$. The negative class is sampled uniformly on the distinct images under $B$; its image-size bound converts between rectangle densities and balanced probabilities.
--
--   Differences from the source:
--   - generalization: positive n and m = n^Δ → every n ≥ 0 and m ≥ 1; reason: the formulas hold for every positive block length, including n = 0 where both input spaces and each nonempty canonical factor are singletons; all source instances are included.
--   - encoding: [m], [n] → Fin m, Fin n; reason: index shift, same instances.
-- source:
--   Gaia Carenini, Bruno Cavalar, Stefan Grosser, Jan Pich, Limits of Lifting, STOC 2027 submission #309 (October 2026), Claim 4.8, printed p. 21 (PDF p. 22)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_LimitsLifting_Approximation_ApproxModel
import Definitions.Def_LimitsLifting_Approximation_CanonicalCover
import Definitions.Def_LimitsLifting_Approximation_RectangleScheme
open MultiplierAssoc206.Resolution

namespace LimitsLifting.Approximation

theorem claim_4_8 {n m : ℕ} (hm : 1 ≤ m) (F : CNF (Fin n)) (hF : StandingCNF F) :
    Function.Injective (encA (m := m) F) ∧
      (1 - 2 * (n : ℝ) * (2 : ℝ) ^ (-(m : ℝ))) * (2 : ℝ) ^ (m * n) ≤
        ((Finset.univ.image (encB (m := m) F)).card : ℝ) := by sorry

end LimitsLifting.Approximation
